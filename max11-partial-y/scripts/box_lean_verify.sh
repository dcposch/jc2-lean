#!/usr/bin/env bash
# Sync this project to the dedicated Lean box and run a fail-closed build.
set -euo pipefail

# Bash may read a script lazily while it runs.  A helper edit during a long
# Lean build can therefore splice old and new bytes into the live interpreter.
# Re-exec an unlinked immutable snapshot so maintenance cannot corrupt a gate.
# This also makes proof verification independent of concurrent helper commits.
if [[ -z "${BOX_LEAN_SELF_SNAPSHOT:-}" ]]; then
  original_project_dir="$(cd "$(dirname "$0")/.." && pwd)"
  script_snapshot="$(mktemp -t box_lean_verify.sh.XXXXXX)"
  cp -p -- "$0" "$script_snapshot"
  export BOX_LEAN_SELF_SNAPSHOT="$script_snapshot"
  export BOX_LEAN_PROJECT_DIR="$original_project_dir"
  exec /bin/bash "$script_snapshot" "$@"
fi
script_snapshot="$BOX_LEAN_SELF_SNAPSHOT"
rm -f -- "$script_snapshot"
project_dir="${BOX_LEAN_PROJECT_DIR:?missing immutable verifier project directory}"

box_host="${BOX_LEAN_HOST:-ubuntu@54.81.66.156}"
box_key="${BOX_LEAN_KEY:-/Users/dc/.ssh/claude-cli.pem}"
box_dir="${BOX_LEAN_DIR:-/home/ubuntu/jc2-lean/max11-partial-y}"
run_axioms=0
full_build=0
receipt_only=0
wait_lock_seconds=0
verbose="${BOX_LEAN_VERBOSE:-0}"
lean_files=()
modules=()

usage() {
  echo "usage: $0 [--full | --file File.lean [--file File.lean ...] | LeanModule ...] [--axioms] [--receipt-only] [--wait-lock SECONDS]" >&2
  echo "  --file: isolated scratch/one-file verification" >&2
  echo "  LeanModule ... --axioms: persistent canonical build and full axiom audit" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --full) full_build=1 ;;
    --receipt-only) receipt_only=1 ;;
    --wait-lock)
      shift
      (($#)) || usage
      [[ "$1" =~ ^[0-9]+$ ]] || usage
      wait_lock_seconds="$1"
      ;;
    --axioms) run_axioms=1 ;;
    --file)
      shift
      (($#)) || usage
      [[ "$1" =~ ^[A-Za-z0-9_.-]+\.lean$ ]] || {
        echo "invalid Lean file name: $1" >&2
        exit 2
      }
      lean_files+=("$1")
      ;;
    --help|-h) usage ;;
    -*) usage ;;
    *)
      [[ "$1" =~ ^[A-Za-z0-9_.-]+$ ]] || {
        echo "invalid Lean module name: $1" >&2
        exit 2
      }
      modules+=("$1")
      ;;
  esac
  shift
done

mode_count=$((full_build + (${#modules[@]} > 0) + (${#lean_files[@]} > 0)))
if ((mode_count != 1)); then
  echo "choose exactly one of --full, --file, or explicit modules" >&2
  exit 2
fi
if ((receipt_only && (${#lean_files[@]} == 0 || run_axioms))); then
  echo "--receipt-only requires --file and cannot be combined with --axioms" >&2
  exit 2
fi
if ((wait_lock_seconds && ${#lean_files[@]} == 0)); then
  echo "--wait-lock is only valid with --file" >&2
  exit 2
fi
[[ -r "$box_key" ]] || {
  echo "missing SSH key: $box_key" >&2
  exit 2
}

ssh_args=(-i "$box_key" -o BatchMode=yes -o StrictHostKeyChecking=no)
rsync_shell="ssh -i $box_key -o BatchMode=yes -o StrictHostKeyChecking=no"
remote_work_dir="$box_dir"
cleanup_remote=0
local_log=""
axiom_log=""
canonical_lock_dir=""
canonical_lock_acquired=0
scratch_lock_dirs=()

cleanup() {
  [[ -z "$local_log" ]] || rm -f "$local_log"
  [[ -z "$axiom_log" ]] || rm -f "$axiom_log"
  if ((cleanup_remote)); then
    # An interrupted SSH client can leave Lean alive in a deleted workspace.
    # Stop only processes whose exact cwd is this validated temporary tree.
    ssh "${ssh_args[@]}" "$box_host" "
      for signal in TERM KILL; do
        for proc in /proc/[0-9]*; do
          cwd=\$(readlink \"\$proc/cwd\" 2>/dev/null || true)
          case \"\$cwd\" in
            '$remote_work_dir'|'$remote_work_dir'/*)
              kill -\"\$signal\" \"\${proc##*/}\" 2>/dev/null || true ;;
          esac
        done
        [[ \"\$signal\" == TERM ]] && sleep 1
      done
      rm -rf -- '$remote_work_dir'
    " >/dev/null 2>&1 || true
  fi
  if ((canonical_lock_acquired)); then
    rmdir "$canonical_lock_dir" >/dev/null 2>&1 || true
  fi
  for scratch_lock_dir in ${scratch_lock_dirs[@]+"${scratch_lock_dirs[@]}"}; do
    rm -f -- "$scratch_lock_dir/owner" >/dev/null 2>&1 || true
    rmdir "$scratch_lock_dir" >/dev/null 2>&1 || true
  done
}
trap cleanup EXIT

# Canonical builds reuse one cached remote checkout.  Syncing or building two
# of them concurrently races both the source tree and Lake artifacts.  Scratch
# gates use isolated workspaces and intentionally do not take this lock.
if ((${#lean_files[@]} == 0)); then
  lock_key="$(printf '%s\n' "$box_host|$box_dir" | LC_ALL=C shasum -a 256 | awk '{print $1}')"
  canonical_lock_dir="${TMPDIR:-/tmp}/box-lean-canonical-${lock_key}.lock"
  if ! mkdir "$canonical_lock_dir"; then
    echo "canonical verifier already running (lock: $canonical_lock_dir)" >&2
    exit 75
  fi
  canonical_lock_acquired=1
elif ((!receipt_only)); then
  # A scratch target has one authoritative compile at a time.  This prevents
  # agents and the root process from spending separate AWS cores and 8+ GiB
  # each elaborating the same leaf.  Different targets remain fully parallel.
  scratch_lock_files=()
  while IFS= read -r scratch_lock_file; do
    scratch_lock_files+=("$scratch_lock_file")
  done < <(printf '%s\n' "${lean_files[@]}" | LC_ALL=C sort -u)
  for scratch_lock_file in "${scratch_lock_files[@]}"; do
    scratch_lock_key="$(printf '%s\n' \
      "$project_dir|$box_host|$box_dir|$scratch_lock_file" | \
      LC_ALL=C shasum -a 256 | awk '{print $1}')"
    scratch_lock_dir="${TMPDIR:-/tmp}/box-lean-scratch-${scratch_lock_key}.lock"
    lock_started="$(date +%s)"
    while ! mkdir "$scratch_lock_dir" 2>/dev/null; do
      lock_owner="$(sed -nE 's/^pid=([0-9]+).*/\1/p' \
        "$scratch_lock_dir/owner" 2>/dev/null || true)"
      if [[ "$lock_owner" =~ ^[0-9]+$ ]] && ! kill -0 "$lock_owner" 2>/dev/null; then
        rm -f -- "$scratch_lock_dir/owner" >/dev/null 2>&1 || true
        rmdir "$scratch_lock_dir" >/dev/null 2>&1 || true
        continue
      elif [[ -z "$lock_owner" ]]; then
        # Recover the tiny mkdir-before-owner crash window without stealing a
        # lock from a live process that is just about to write its owner file.
        sleep 0.1
        if [[ ! -s "$scratch_lock_dir/owner" ]]; then
          rmdir "$scratch_lock_dir" >/dev/null 2>&1 || true
          continue
        fi
      fi
      lock_elapsed=$(($(date +%s) - lock_started))
      if ((lock_elapsed >= wait_lock_seconds)); then
        echo "scratch verifier already running for $scratch_lock_file (lock: $scratch_lock_dir)" >&2
        exit 75
      fi
      sleep 2
    done
    printf '%s\n' "pid=$$ file=$scratch_lock_file started=$(date -u +%FT%TZ)" \
      >"$scratch_lock_dir/owner"
    scratch_lock_dirs+=("$scratch_lock_dir")
  done
fi

scratch_compile_files=()
source_hashes=()
scratch_cache_keys=()
scratch_legacy_cache_keys=()
scratch_closure_legacy_cache_keys=()
environment_walk_seen=()
tracked_dependency_files=()
tracked_environment_hash=""
gate_fingerprint=""
gate_receipt=""
gate_failure_log=""
if ((${#lean_files[@]})); then
  hash_tracked_environment() {
    (
      cd "$project_dir"
      for tracked_file in lean-toolchain lake-manifest.json; do
        [[ -f "$tracked_file" ]] || continue
        printf '%s\0' "$tracked_file"
        LC_ALL=C shasum -a 256 "$tracked_file"
      done
      for tracked_file in "${tracked_dependency_files[@]}"; do
        printf '%s\0' "$tracked_file"
        LC_ALL=C shasum -a 256 "$tracked_file"
      done
    ) | LC_ALL=C shasum -a 256 | awk '{print $1}'
  }

  collect_environment_imports() {
    local source="$1"
    local known module dependency
    for known in ${environment_walk_seen[@]+"${environment_walk_seen[@]}"}; do
      [[ "$known" == "$source" ]] && return
    done
    environment_walk_seen+=("$source")
    if git -C "$project_dir" ls-files --error-unmatch -- \
        "$source" >/dev/null 2>&1; then
      tracked_dependency_files+=("$source")
    fi
    while IFS= read -r module; do
      [[ "$module" =~ ^[A-Za-z0-9_.]+$ ]] || continue
      dependency="${module//./\/}.lean"
      [[ -f "$project_dir/$dependency" ]] || continue
      collect_environment_imports "$dependency"
    done < <(sed -nE 's/^import[[:space:]]+([A-Za-z0-9_.]+)[[:space:]]*$/\1/p' \
      "$project_dir/$source")
  }

  collect_local_imports() {
    local source="$1"
    local known module dependency
    for known in ${scratch_compile_files[@]+"${scratch_compile_files[@]}"}; do
      [[ "$known" == "$source" ]] && return
    done
    while IFS= read -r module; do
      [[ "$module" =~ ^[A-Za-z0-9_.]+$ ]] || continue
      dependency="${module//./\/}.lean"
      if [[ -f "$project_dir/$dependency" ]]; then
        if [[ "$dependency" == *Scratch.lean ]] ||
            ! git -C "$project_dir" ls-files --error-unmatch -- \
              "$dependency" >/dev/null 2>&1; then
          collect_local_imports "$dependency"
        fi
      fi
    done < <(sed -nE 's/^import[[:space:]]+([A-Za-z0-9_.]+)[[:space:]]*$/\1/p' \
      "$project_dir/$source")
    scratch_compile_files+=("$source")
  }

  for lean_file in "${lean_files[@]}"; do
    [[ -f "$project_dir/$lean_file" ]] || {
      echo "missing Lean file: $project_dir/$lean_file" >&2
      exit 2
    }
    collect_local_imports "$lean_file"
    collect_environment_imports "$lean_file"
  done
  # Catch placeholders locally and surface generated declarations likely to
  # exhaust Lean's default heartbeat budget before paying for a remote gate.
  (
    cd "$project_dir"
    ./scripts/max11_lean_preflight.sh --strict "${lean_files[@]}"
  )
  for source in "${scratch_compile_files[@]}"; do
    source_hashes+=("$(LC_ALL=C shasum -a 256 "$project_dir/$source" | awk '{print $1}')")
  done
  tracked_environment_hash="$(hash_tracked_environment)"
  gate_fingerprint="$({
    printf 'tracked_environment=%s\naxioms=%s\n' "$tracked_environment_hash" "$run_axioms"
    for ((i = 0; i < ${#scratch_compile_files[@]}; i++)); do
      printf 'file=%s sha256=%s\n' \
        "${scratch_compile_files[$i]}" "${source_hashes[$i]}"
    done
  } | LC_ALL=C shasum -a 256 | awk '{print $1}')"
  gate_receipt="$project_dir/.max11-lanes/gates/$gate_fingerprint.receipt"
  gate_failure_log="$project_dir/.max11-lanes/gates/$gate_fingerprint.failure.log"
  if ((receipt_only)); then
    if [[ -s "$gate_receipt" ]] &&
        grep -Fxq "GATE_RECEIPT_SHA256=$gate_fingerprint" "$gate_receipt" &&
        grep -Fxq "BUILD_EXIT=0 ERROR_COUNT=0 SORRYAX_COUNT=0" "$gate_receipt"; then
      cat "$gate_receipt"
      exit 0
    fi
    echo "GATE_RECEIPT_MISSING SHA256=$gate_fingerprint" >&2
    exit 66
  fi
  # Cache each module against its own recursive scratch import closure.  The
  # old cumulative-prefix key made an artifact depend on unrelated imports
  # visited earlier in another root file, causing expensive false misses.
  # Retain that legacy key alongside the new key for a gradual cache migration.
  collect_cache_closure() {
    local source="$1"
    local known module dependency
    for known in ${cache_walk_seen[@]+"${cache_walk_seen[@]}"}; do
      [[ "$known" == "$source" ]] && return
    done
    cache_walk_seen+=("$source")
    while IFS= read -r module; do
      [[ "$module" =~ ^[A-Za-z0-9_.]+$ ]] || continue
      dependency="${module//./\/}.lean"
      if [[ -f "$project_dir/$dependency" ]] &&
          { [[ "$dependency" == *Scratch.lean ]] ||
            ! git -C "$project_dir" ls-files --error-unmatch -- \
              "$dependency" >/dev/null 2>&1; }; then
        collect_cache_closure "$dependency"
      fi
    done < <(sed -nE 's/^import[[:space:]]+([A-Za-z0-9_.]+)[[:space:]]*$/\1/p' \
      "$project_dir/$source")
    cache_closure_files+=("$source")
  }

  legacy_cache_state="$tracked_environment_hash"
  for ((i = 0; i < ${#scratch_compile_files[@]}; i++)); do
    legacy_cache_state="$(printf '%s\n%s\n%s\n' \
      "$legacy_cache_state" "${scratch_compile_files[$i]}" "${source_hashes[$i]}" \
      | LC_ALL=C shasum -a 256 | awk '{print $1}')"
    scratch_legacy_cache_keys+=("$legacy_cache_state")

    cache_walk_seen=()
    cache_closure_files=()
    collect_cache_closure "${scratch_compile_files[$i]}"
    closure_legacy_cache_state="$tracked_environment_hash"
    for cache_source in "${cache_closure_files[@]}"; do
      closure_legacy_cache_state="$(printf '%s\n%s\n%s\n' \
        "$closure_legacy_cache_state" "$cache_source" \
        "$(LC_ALL=C shasum -a 256 "$project_dir/$cache_source" | awk '{print $1}')" \
        | LC_ALL=C shasum -a 256 | awk '{print $1}')"
    done
    scratch_closure_legacy_cache_keys+=("$closure_legacy_cache_state")
    closure_cache_key="$({
      printf 'tracked_environment=%s\n' "$tracked_environment_hash"
      for cache_source in "${cache_closure_files[@]}"; do
        printf 'file=%s sha256=%s\n' "$cache_source" \
          "$(LC_ALL=C shasum -a 256 "$project_dir/$cache_source" | awk '{print $1}')"
      done
    } | LC_ALL=C shasum -a 256 | awk '{print $1}')"
    scratch_cache_keys+=("$closure_cache_key")
  done

  remote_parent="${box_dir%/*}"
  remote_work_dir="$(ssh "${ssh_args[@]}" "$box_host" \
    "mktemp -d '$remote_parent/box-lean-verify.XXXXXX'")"
  remote_suffix="${remote_work_dir#"$remote_parent/box-lean-verify."}"
  [[ "$remote_work_dir" == "$remote_parent/box-lean-verify.$remote_suffix" &&
      "$remote_suffix" =~ ^[A-Za-z0-9]+$ ]] || {
    echo "unsafe remote temporary directory: $remote_work_dir" >&2
    exit 2
  }
  cleanup_remote=1
  ssh "${ssh_args[@]}" "$box_host" \
    "mkdir -p '$box_dir/.scratch-olean-cache' && \
     ln -s '$box_dir/.lake' '$remote_work_dir/.lake'"
fi

if ((${#lean_files[@]})); then
  echo "FILES ${lean_files[*]} COMPILE_COUNT=${#scratch_compile_files[@]} TRACKED_ENV_SHA256=$tracked_environment_hash"
fi
echo "SYNC $project_dir -> $box_host:$remote_work_dir"
rsync -az \
  --exclude .git \
  --exclude .lake \
  --exclude '*.olean' \
  -e "$rsync_shell" \
  "$project_dir/" "$box_host:$remote_work_dir/"

if ((${#lean_files[@]})); then
  build_command=""
  for ((i = 0; i < ${#scratch_compile_files[@]}; i++)); do
    source="${scratch_compile_files[$i]}"
    output="${source%.lean}.olean"
    cache_file="$box_dir/.scratch-olean-cache/${scratch_cache_keys[$i]}.olean"
    legacy_cache_file="$box_dir/.scratch-olean-cache/${scratch_legacy_cache_keys[$i]}.olean"
    closure_legacy_cache_file="$box_dir/.scratch-olean-cache/${scratch_closure_legacy_cache_keys[$i]}.olean"
    requested=0
    for lean_file in "${lean_files[@]}"; do
      [[ "$source" == "$lean_file" ]] && requested=1
    done
    [[ -z "$build_command" ]] || build_command+=" && "
    # Lake's generated LEAN_PATH omits the current directory.  Preserve it so
    # a later scratch target can import an earlier untracked `.olean` compiled
    # in this isolated workspace.  Exact-source dependency artifacts are
    # content-addressed by the tracked Lean environment and ordered scratch
    # ancestry.  The requested leaf is always rebuilt, never accepted from
    # cache, so every successful gate still elaborates the claimed theorem.
    compile_and_cache="env LEAN_PATH=. lake env lean -R . -o $output $source && \
      cp '$output' '$cache_file.tmp.\$\$' && mv -f '$cache_file.tmp.\$\$' '$cache_file'"
    if ((requested)); then
      build_command+="$compile_and_cache && echo SCRATCH_CACHE_LEAF FILE=$source"
    else
      build_command+="if [[ -s '$cache_file' ]]; then \
        cp '$cache_file' '$output' && echo SCRATCH_CACHE_HIT FILE=$source; \
        elif [[ -s '$legacy_cache_file' ]]; then \
        cp '$legacy_cache_file' '$output' && cp '$legacy_cache_file' '$cache_file' && \
          echo SCRATCH_CACHE_LEGACY_HIT FILE=$source; \
        elif [[ -s '$closure_legacy_cache_file' ]]; then \
        cp '$closure_legacy_cache_file' '$output' && \
          cp '$closure_legacy_cache_file' '$cache_file' && \
          echo SCRATCH_CACHE_CLOSURE_LEGACY_HIT FILE=$source; \
        else $compile_and_cache && echo SCRATCH_CACHE_MISS FILE=$source; fi"
    fi
  done
elif ((full_build)); then
  build_command="lake build"
else
  build_command="lake build ${modules[*]}"
fi

local_log="$(mktemp -t box-lean-build.XXXXXX)"
axiom_log="$(mktemp -t box-lean-axioms.XXXXXX)"

set +e
# A deep scratch closure can make `build_command` hundreds of KiB.  Passing it
# as SSH's remote-command argument eventually hits an exec(2) argv limit even
# though every individual Lean command is small.  Stream a Bash program over
# stdin instead, leaving SSH's own argv constant-sized for arbitrarily deep
# proof towers.
{
  printf 'set -euo pipefail\n'
  printf 'cd %q\n' "$remote_work_dir"
  printf 'export PATH=/home/ubuntu/.elan/bin:$PATH\n'
  printf '%s\n' "$build_command"
} | ssh "${ssh_args[@]}" "$box_host" /bin/bash >"$local_log" 2>&1
build_exit=${PIPESTATUS[1]}
set -e
error_count="$(grep -cE 'error:|error\(' "$local_log" || true)"
sorry_count="$(grep -c 'sorryAx' "$local_log" || true)"
echo "BUILD_EXIT=$build_exit ERROR_COUNT=$error_count SORRYAX_COUNT=$sorry_count"
if ((build_exit != 0 || error_count != 0 || sorry_count != 0)); then
  if [[ -n "$gate_failure_log" ]]; then
    mkdir -p "${gate_failure_log%/*}"
    failure_tmp="$gate_failure_log.tmp.$$"
    cp -p -- "$local_log" "$failure_tmp"
    mv -f -- "$failure_tmp" "$gate_failure_log"
    echo "FAILURE_LOG=$gate_failure_log"
  fi
  # Generated polynomial goals routinely span more than eight lines.  Keep
  # enough context in the terminal for diagnosis while retaining the complete
  # immutable-fingerprint log above for exact follow-up work.
  if ! grep -n -B 8 -A 30 -E 'error:|error\(|sorryAx' "$local_log"; then
    tail -n 160 "$local_log"
  fi
  exit 1
fi
[[ -z "$gate_failure_log" ]] || rm -f -- "$gate_failure_log"
if [[ "$verbose" == 1 ]]; then
  cat "$local_log"
else
  tail -n 3 "$local_log"
fi

if ((run_axioms)); then
  set +e
  ssh "${ssh_args[@]}" "$box_host" \
    "cd '$remote_work_dir' && export PATH=/home/ubuntu/.elan/bin:\$PATH && ./scripts/check_axioms.sh" \
    >"$axiom_log" 2>&1
  axiom_exit=$?
  set -e
  axiom_error_count="$(grep -cE 'error:|error\(' "$axiom_log" || true)"
  axiom_sorry_count="$(grep -c 'sorryAx' "$axiom_log" || true)"
  echo "AXIOM_EXIT=$axiom_exit ERROR_COUNT=$axiom_error_count SORRYAX_COUNT=$axiom_sorry_count"
  if ((axiom_exit != 0 || axiom_error_count != 0 || axiom_sorry_count != 0)); then
    if ! grep -n -B 8 -A 30 -E 'error:|error\(|sorryAx' "$axiom_log"; then
      tail -n 80 "$axiom_log"
    fi
    exit 1
  fi
  if [[ "$verbose" == 1 ]]; then
    cat "$axiom_log"
  else
    tail -n 2 "$axiom_log"
  fi
fi

if ((${#lean_files[@]})); then
  current_tracked_environment_hash="$(hash_tracked_environment)"
  if [[ "$current_tracked_environment_hash" != "$tracked_environment_hash" ]]; then
    echo "TRACKED_ENVIRONMENT_CHANGED_DURING_VERIFY" >&2
    echo "EXPECTED_SHA256=$tracked_environment_hash CURRENT_SHA256=$current_tracked_environment_hash" >&2
    exit 1
  fi
  for ((i = 0; i < ${#scratch_compile_files[@]}; i++)); do
    current_hash="$(LC_ALL=C shasum -a 256 "$project_dir/${scratch_compile_files[$i]}" | awk '{print $1}')"
    if [[ "$current_hash" != "${source_hashes[$i]}" ]]; then
      echo "SOURCE_CHANGED_DURING_VERIFY FILE=${scratch_compile_files[$i]}" >&2
      echo "EXPECTED_SHA256=${source_hashes[$i]} CURRENT_SHA256=$current_hash" >&2
      exit 1
    fi
    echo "VERIFIED_SHA256=$current_hash FILE=${scratch_compile_files[$i]}"
  done
  mkdir -p "${gate_receipt%/*}"
  receipt_tmp="$gate_receipt.tmp.$$"
  {
    echo "GATE_RECEIPT_SHA256=$gate_fingerprint"
    echo "TRACKED_ENV_SHA256=$tracked_environment_hash"
    echo "BUILD_EXIT=0 ERROR_COUNT=0 SORRYAX_COUNT=0"
    for ((i = 0; i < ${#scratch_compile_files[@]}; i++)); do
      echo "VERIFIED_SHA256=${source_hashes[$i]} FILE=${scratch_compile_files[$i]}"
    done
    echo "VERIFIED_AT=$(date -u +%FT%TZ)"
  } >"$receipt_tmp"
  mv -f "$receipt_tmp" "$gate_receipt"
  echo "GATE_RECEIPT=$gate_receipt"
fi
