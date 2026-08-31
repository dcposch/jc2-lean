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
reuse_receipt=0
retry_known_failure=0
wait_lock_seconds=0
verbose="${BOX_LEAN_VERBOSE:-0}"
compile_timeout_seconds="${BOX_LEAN_COMPILE_TIMEOUT_SECONDS:-1800}"
profile=0
lean_files=()
modules=()

usage() {
  echo "usage: $0 [--full | --file File.lean [--file File.lean ...] | LeanModule ...] [--axioms] [--profile] [--receipt-only] [--reuse-receipt] [--retry-known-failure] [--wait-lock SECONDS]" >&2
  echo "  --file: isolated scratch/one-file verification" >&2
  echo "  LeanModule ... --axioms: persistent canonical build and full axiom audit" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --full) full_build=1 ;;
    --receipt-only) receipt_only=1 ;;
    --reuse-receipt) reuse_receipt=1 ;;
    --retry-known-failure) retry_known_failure=1 ;;
    --profile) profile=1 ;;
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
if ((reuse_receipt && (${#lean_files[@]} == 0 || run_axioms || receipt_only))); then
  echo "--reuse-receipt requires --file and cannot be combined with --axioms or --receipt-only" >&2
  exit 2
fi
if ((retry_known_failure && ${#lean_files[@]} == 0)); then
  echo "--retry-known-failure is only valid with --file" >&2
  exit 2
fi
if ((wait_lock_seconds && ${#lean_files[@]} == 0)); then
  echo "--wait-lock is only valid with --file" >&2
  exit 2
fi
if ((profile && ${#lean_files[@]} == 0)); then
  echo "--profile is currently supported only with --file" >&2
  exit 2
fi
[[ -r "$box_key" ]] || {
  echo "missing SSH key: $box_key" >&2
  exit 2
}
[[ "$compile_timeout_seconds" =~ ^[1-9][0-9]*$ ]] || {
  echo "BOX_LEAN_COMPILE_TIMEOUT_SECONDS must be a positive integer" >&2
  exit 2
}

# A scratch gate used to establish several fresh SSH connections (workspace
# setup, rsync, compile, cleanup).  Lean itself often needs only a few seconds,
# so those handshakes were a material fraction of the iteration loop.  Share a
# short-lived OpenSSH master across verifier processes; `%C` keeps the socket
# path deterministic without exposing or lengthening the host/key tuple.
box_control_path="${BOX_LEAN_SSH_CONTROL_PATH:-/tmp/box-lean-ssh-%C}"
ssh_args=(-i "$box_key" -o BatchMode=yes -o StrictHostKeyChecking=no
  -o ControlMaster=auto -o ControlPersist=600 -o "ControlPath=$box_control_path")
rsync_shell="ssh -i $box_key -o BatchMode=yes -o StrictHostKeyChecking=no -o ControlMaster=auto -o ControlPersist=600 -o ControlPath=$box_control_path"

# macOS `shasum` starts a Perl interpreter for every file.  Deep scratch gates
# hash a source once before and once after verification, so use the system C
# implementation while preserving the exact SHA-256 bytes and record format.
sha256_stream() {
  local digest
  digest="$(openssl dgst -sha256 -r)"
  printf '%s\n' "${digest%% *}"
}

sha256_file() {
  local digest
  digest="$(openssl dgst -sha256 -r "$1")"
  printf '%s\n' "${digest%% *}"
}

sha256_file_record() {
  printf '%s  %s\n' "$(sha256_file "$1")" "$1"
}

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
  lock_key="$(printf '%s\n' "$box_host|$box_dir" | sha256_stream)"
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
      sha256_stream)"
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
        sha256_file_record "$tracked_file"
      done
      # macOS still ships Bash 3.2, where expanding a declared-but-empty array
      # under `set -u` raises an unbound-variable error.
      for tracked_file in \
          ${tracked_dependency_files[@]+"${tracked_dependency_files[@]}"}; do
        printf '%s\0' "$tracked_file"
        sha256_file_record "$tracked_file"
      done
    ) | sha256_stream
  }

  collect_environment_imports() {
    local source="$1"
    local known module dependency scratch_source in_scratch_closure=0
    for known in ${environment_walk_seen[@]+"${environment_walk_seen[@]}"}; do
      [[ "$known" == "$source" ]] && return
    done
    environment_walk_seen+=("$source")
    for scratch_source in \
        ${scratch_compile_files[@]+"${scratch_compile_files[@]}"}; do
      if [[ "$scratch_source" == "$source" ]]; then
        in_scratch_closure=1
        break
      fi
    done
    if (( ! in_scratch_closure )) && \
        git -C "$project_dir" ls-files --error-unmatch -- \
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
  # A receipt-only query cannot create or update an attestation: exact source
  # and environment hashes below either find a prior successful receipt or
  # fail closed.  Re-running the multi-second collision/preflight walk for
  # every dependency handoff therefore adds latency without adding assurance.
  if ((!receipt_only)); then
    (
      cd "$project_dir"
      ./scripts/max11_lean_preflight.sh --strict "${lean_files[@]}"
    )
  fi
  for source in "${scratch_compile_files[@]}"; do
    source_hashes+=("$(sha256_file "$project_dir/$source")")
  done
  tracked_environment_hash="$(hash_tracked_environment)"
  gate_fingerprint="$({
    printf 'tracked_environment=%s\naxioms=%s\n' "$tracked_environment_hash" "$run_axioms"
    for ((i = 0; i < ${#scratch_compile_files[@]}; i++)); do
      printf 'file=%s sha256=%s\n' \
        "${scratch_compile_files[$i]}" "${source_hashes[$i]}"
    done
  } | sha256_stream)"
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
    if [[ -s "$gate_failure_log" ]] &&
        grep -Eq 'error:|error\(' "$gate_failure_log"; then
      error_count="$(grep -cE 'error:|error\(' "$gate_failure_log" || true)"
      sorry_count="$(grep -c 'sorryAx' "$gate_failure_log" || true)"
      echo "GATE_FAILURE_KNOWN SHA256=$gate_fingerprint ERROR_COUNT=$error_count SORRYAX_COUNT=$sorry_count" >&2
      echo "FAILURE_LOG=$gate_failure_log" >&2
      grep -m 1 -E 'error:|error\(' "$gate_failure_log" >&2 || true
      exit 1
    fi
    exit 66
  fi
  # Automated lane/recovery callers may have waited behind another exact gate.
  # Recheck the immutable success receipt after taking the per-target lock so a
  # waiter does not elaborate the leaf a second time. Manual gates omit this
  # option and continue to rebuild the requested leaf authoritatively.
  if ((reuse_receipt)) && [[ -s "$gate_receipt" ]] &&
      grep -Fxq "GATE_RECEIPT_SHA256=$gate_fingerprint" "$gate_receipt" &&
      grep -Fxq "BUILD_EXIT=0 ERROR_COUNT=0 SORRYAX_COUNT=0" "$gate_receipt"; then
    echo "SUCCESS_RECEIPT_REUSED_AFTER_WAIT SHA256=$gate_fingerprint"
    cat "$gate_receipt"
    exit 0
  fi
  # A gate fingerprint commits to the tracked Lean environment and the exact
  # recursive scratch source closure.  A previous Lean diagnostic for that
  # fingerprint is therefore deterministic and can be returned before paying
  # the SSH/rsync/elaboration cost again.  Infrastructure failures are never
  # accepted here because they do not contain a Lean `error:` diagnostic.
  if ((!retry_known_failure)) && [[ -s "$gate_failure_log" ]] &&
      grep -Eq 'error:|error\(' "$gate_failure_log"; then
    error_count="$(grep -cE 'error:|error\(' "$gate_failure_log" || true)"
    sorry_count="$(grep -c 'sorryAx' "$gate_failure_log" || true)"
    echo "KNOWN_FAILURE_RECEIPT_HIT SHA256=$gate_fingerprint"
    echo "BUILD_EXIT=1 ERROR_COUNT=$error_count SORRYAX_COUNT=$sorry_count"
    echo "FAILURE_LOG=$gate_failure_log"
    if ! grep -n -B 8 -A 30 -E 'error:|error\(|sorryAx' "$gate_failure_log"; then
      tail -n 160 "$gate_failure_log"
    fi
    exit 1
  fi
  # Cache each module against its exact recursive source and tracked import
  # closure.  Doing this as nested Bash DFS walks was effectively cubic on a
  # long linear tower: a 109-module lane spent minutes computing keys before
  # its five-second Lean leaf even started.  One memoized graph pass preserves
  # the byte-for-byte key format and takes well under a second on that tower.
  cache_key_records="$(python3 "$project_dir/scripts/max11_scratch_cache_keys.py" \
    --project-dir "$project_dir" "${scratch_compile_files[@]}")"
  cache_key_index=0
  while IFS=$'\t' read -r cache_tag cache_source cache_source_hash cache_key \
      legacy_cache_key; do
    [[ "$cache_tag" == MODULE ]] || {
      echo "invalid scratch cache-key record tag: $cache_tag" >&2
      exit 1
    }
    [[ "$cache_source" == "${scratch_compile_files[$cache_key_index]}" ]] || {
      echo "scratch cache-key source order mismatch: $cache_source" >&2
      exit 1
    }
    [[ "$cache_source_hash" == "${source_hashes[$cache_key_index]}" ]] || {
      echo "scratch cache-key source hash mismatch: $cache_source" >&2
      exit 1
    }
    [[ "$cache_key" =~ ^[0-9a-f]{64}$ ]] || {
      echo "invalid scratch cache key: $cache_source" >&2
      exit 1
    }
    [[ "$legacy_cache_key" =~ ^[0-9a-f]{64}$ ]] || {
      echo "invalid legacy scratch cache key: $cache_source" >&2
      exit 1
    }
    scratch_cache_keys+=("$cache_key")
    scratch_legacy_cache_keys+=("$legacy_cache_key")
    cache_key_index=$((cache_key_index + 1))
  done <<<"$cache_key_records"
  ((cache_key_index == ${#scratch_compile_files[@]})) || {
    echo "scratch cache-key record count mismatch" >&2
    exit 1
  }

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
rsync_excludes=(
  --exclude .git
  --exclude .lake
  --exclude .max11-lanes
  --exclude '*.olean'
)
if ((${#lean_files[@]})); then
  # Isolated scratch gates need only their already-computed recursive local
  # import closure.  Uploading every unrelated scratch lane and the growing
  # local ledger made each fresh remote workspace needlessly expensive and
  # allowed unrelated generated files to leak into its filesystem view.
  rsync_excludes+=(--exclude '*Scratch.lean')
fi
rsync -az "${rsync_excludes[@]}" -e "$rsync_shell" \
  "$project_dir/" "$box_host:$remote_work_dir/"
if ((${#lean_files[@]})); then
  printf '%s\0' "${scratch_compile_files[@]}" | \
    rsync -az --from0 --files-from=- -e "$rsync_shell" \
      "$project_dir/" "$box_host:$remote_work_dir/"
  echo "SYNC_SCRATCH_CLOSURE COUNT=${#scratch_compile_files[@]}"
fi

if ((${#lean_files[@]})); then
  build_command=""
  for ((i = 0; i < ${#scratch_compile_files[@]}; i++)); do
    source="${scratch_compile_files[$i]}"
    output="${source%.lean}.olean"
    cache_file="$box_dir/.scratch-olean-cache/${scratch_cache_keys[$i]}.olean"
    legacy_cache_file="$box_dir/.scratch-olean-cache/${scratch_legacy_cache_keys[$i]}.olean"
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
    if ((requested)); then
      printf -v cache_step 'compile_scratch_leaf %q %q %q' \
        "$cache_file" "$output" "$source"
      build_command+="$cache_step"
    else
      printf -v cache_step 'load_or_compile_scratch_dependency %q %q %q %q' \
        "$cache_file" "$legacy_cache_file" "$output" "$source"
      build_command+="$cache_step"
    fi
  done
elif ((full_build)); then
  build_command="lake build"
else
  build_command="lake build ${modules[*]}"
fi

local_log="$(mktemp -t box-lean-build.XXXXXX)"
axiom_log="$(mktemp -t box-lean-axioms.XXXXXX)"

# Normal authoritative gates retain the historical quiet behavior.  A
# profiled diagnostic gate tees Lean's declaration timings into the durable
# lane log as they arrive, so owners can locate a pathological declaration
# without waiting for the whole compile or timeout.
capture_build_output() {
  if ((profile)); then
    tee "$local_log"
  else
    cat >"$local_log"
  fi
}

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
  printf 'export BOX_LEAN_COMPILE_TIMEOUT_SECONDS=%q\n' \
    "$compile_timeout_seconds"
  printf 'export BOX_LEAN_PROFILE=%q\n' "$profile"
  if ((${#lean_files[@]})); then
    # Independent isolated gates can share a deep scratch dependency.  The
    # content-addressed cache prevents repeat work only after an artifact has
    # landed; without a per-key lock, simultaneous misses still elaborate the
    # same module in parallel and each consume 8--17 GiB.  Linux flock is tied
    # to the process/file descriptor, so interruption releases it without a
    # stale-directory recovery protocol.  Recheck the cache after waiting.
    cat <<'REMOTE_CACHE_HELPERS'
load_or_compile_scratch_dependency() {
  local cache_file="$1"
  local legacy_cache_file="$2"
  local output="$3"
  local source="$4"
  if [[ ! -s "$cache_file" && "$legacy_cache_file" != "$cache_file" && \
        -s "$legacy_cache_file" ]]; then
    # Before the content-stable key fix, committing byte-identical scratch
    # source changed only the cache namespace.  The legacy key is computed
    # from the same exact recursive source and import hashes, so promote the
    # immutable artifact atomically instead of elaborating it again.
    local promote_tmp="${cache_file}.tmp.promote.$$"
    trap 'rm -f -- "$promote_tmp"' RETURN
    ln -- "$legacy_cache_file" "$promote_tmp" 2>/dev/null || \
      cp -- "$legacy_cache_file" "$promote_tmp"
    mv -f -- "$promote_tmp" "$cache_file"
    trap - RETURN
    printf 'SCRATCH_CACHE_LEGACY_PROMOTED FILE=%s\n' "$source"
  fi
  if [[ -s "$cache_file" ]]; then
    # The content-addressed cache and isolated workspaces normally share one
    # filesystem.  A hard link makes deep 100+ module proof towers hydrate in
    # O(metadata) instead of copying several GiB before every leaf check.  The
    # artifacts are immutable; retain a copy fallback for alternate mounts.
    ln -- "$cache_file" "$output" 2>/dev/null || cp -- "$cache_file" "$output"
    printf 'SCRATCH_CACHE_HIT FILE=%s\n' "$source"
    return
  fi
  /usr/bin/flock "${cache_file}.lock" /bin/bash -s -- \
      "$cache_file" "$output" "$source" <<'REMOTE_CACHE_DEPENDENCY'
set -euo pipefail
cache_file="$1"
output="$2"
source="$3"
failure_file="${cache_file}.failure.log"
metrics_root="${cache_file%/*}/metrics"
mkdir -p "$metrics_root"
metrics_file="$metrics_root/${cache_file##*/}.$(date -u +%Y%m%dT%H%M%SZ).$$.metrics"
metrics_tmp="${metrics_file}.tmp"
if [[ -s "$cache_file" ]]; then
  ln -- "$cache_file" "$output" 2>/dev/null || cp -- "$cache_file" "$output"
  printf 'SCRATCH_CACHE_WAIT_HIT FILE=%s\n' "$source"
elif [[ -s "$failure_file" ]]; then
  printf 'SCRATCH_FAILURE_CACHE_HIT FILE=%s\n' "$source"
  cat -- "$failure_file"
  exit 1
else
  failure_tmp="${failure_file}.tmp.$$"
  trap 'rm -f -- "$failure_tmp" "$metrics_tmp"' EXIT
  set +e
  lean_profile_args=()
  [[ "${BOX_LEAN_PROFILE:-0}" == 1 ]] && lean_profile_args+=(--profile)
  if [[ "${BOX_LEAN_PROFILE:-0}" == 1 ]]; then
    /usr/bin/time -v -o "$metrics_tmp" \
      timeout --signal=TERM --kill-after=30s \
        "$BOX_LEAN_COMPILE_TIMEOUT_SECONDS" \
        env LEAN_PATH=. lake env lean "${lean_profile_args[@]}" -R . -o "$output" "$source" \
      2>&1 | tee "$failure_tmp"
    lean_exit=${PIPESTATUS[0]}
  else
    /usr/bin/time -v -o "$metrics_tmp" \
      timeout --signal=TERM --kill-after=30s \
        "$BOX_LEAN_COMPILE_TIMEOUT_SECONDS" \
        env LEAN_PATH=. lake env lean "${lean_profile_args[@]}" -R . -o "$output" "$source" \
      >"$failure_tmp" 2>&1
    lean_exit=$?
  fi
  set -e
  if ((lean_exit == 124)); then
    printf 'LEAN_COMPILE_TIMEOUT FILE=%s SECONDS=%s\n' \
      "$source" "$BOX_LEAN_COMPILE_TIMEOUT_SECONDS" >>"$failure_tmp"
  fi
  printf '\nSOURCE=%s\nRESULT=%s\n' "$source" "$lean_exit" >>"$metrics_tmp"
  mv -f -- "$metrics_tmp" "$metrics_file"
  [[ "${BOX_LEAN_PROFILE:-0}" == 1 ]] || cat -- "$failure_tmp"
  if ((lean_exit != 0)); then
    # Only memoize diagnostics produced by Lean itself. Transport failures,
    # signals, and host faults remain retryable on the next invocation.
    if grep -Eq 'error:|error\(' "$failure_tmp"; then
      mv -f -- "$failure_tmp" "$failure_file"
      trap - EXIT
      printf 'SCRATCH_FAILURE_CACHE_STORE FILE=%s\n' "$source"
    fi
    exit "$lean_exit"
  fi
  cache_tmp="${cache_file}.tmp.$$"
  trap 'rm -f -- "$cache_tmp" "$failure_tmp"' EXIT
  ln -- "$output" "$cache_tmp" 2>/dev/null || cp -- "$output" "$cache_tmp"
  mv -f -- "$cache_tmp" "$cache_file"
  rm -f -- "$failure_file"
  trap - EXIT
  rm -f -- "$failure_tmp"
  printf 'SCRATCH_CACHE_MISS FILE=%s\n' "$source"
fi
REMOTE_CACHE_DEPENDENCY
}

compile_scratch_leaf() {
  local cache_file="$1"
  local output="$2"
  local source="$3"
  # A requested leaf is deliberately elaborated even when an exact artifact
  # exists: the gate attests to this invocation, not merely cache presence.
  # Taking the same key lock still prevents a concurrent dependency compiler
  # from doing identical work at the same time.
  /usr/bin/flock "${cache_file}.lock" /bin/bash -s -- \
      "$cache_file" "$output" "$source" <<'REMOTE_CACHE_LEAF'
set -euo pipefail
cache_file="$1"
output="$2"
source="$3"
failure_file="${cache_file}.failure.log"
metrics_root="${cache_file%/*}/metrics"
mkdir -p "$metrics_root"
metrics_file="$metrics_root/${cache_file##*/}.$(date -u +%Y%m%dT%H%M%SZ).$$.metrics"
metrics_tmp="${metrics_file}.tmp"
if [[ -s "$failure_file" ]]; then
  printf 'SCRATCH_FAILURE_CACHE_HIT FILE=%s\n' "$source"
  cat -- "$failure_file"
  exit 1
fi
failure_tmp="${failure_file}.tmp.$$"
trap 'rm -f -- "$failure_tmp" "$metrics_tmp"' EXIT
set +e
lean_profile_args=()
[[ "${BOX_LEAN_PROFILE:-0}" == 1 ]] && lean_profile_args+=(--profile)
if [[ "${BOX_LEAN_PROFILE:-0}" == 1 ]]; then
  /usr/bin/time -v -o "$metrics_tmp" \
    timeout --signal=TERM --kill-after=30s \
      "$BOX_LEAN_COMPILE_TIMEOUT_SECONDS" \
      env LEAN_PATH=. lake env lean "${lean_profile_args[@]}" -R . -o "$output" "$source" \
    2>&1 | tee "$failure_tmp"
  lean_exit=${PIPESTATUS[0]}
else
  /usr/bin/time -v -o "$metrics_tmp" \
    timeout --signal=TERM --kill-after=30s \
      "$BOX_LEAN_COMPILE_TIMEOUT_SECONDS" \
      env LEAN_PATH=. lake env lean "${lean_profile_args[@]}" -R . -o "$output" "$source" \
    >"$failure_tmp" 2>&1
  lean_exit=$?
fi
set -e
if ((lean_exit == 124)); then
  printf 'LEAN_COMPILE_TIMEOUT FILE=%s SECONDS=%s\n' \
    "$source" "$BOX_LEAN_COMPILE_TIMEOUT_SECONDS" >>"$failure_tmp"
fi
printf '\nSOURCE=%s\nRESULT=%s\n' "$source" "$lean_exit" >>"$metrics_tmp"
mv -f -- "$metrics_tmp" "$metrics_file"
[[ "${BOX_LEAN_PROFILE:-0}" == 1 ]] || cat -- "$failure_tmp"
if ((lean_exit != 0)); then
  if grep -Eq 'error:|error\(' "$failure_tmp"; then
    mv -f -- "$failure_tmp" "$failure_file"
    trap - EXIT
    printf 'SCRATCH_FAILURE_CACHE_STORE FILE=%s\n' "$source"
  fi
  exit "$lean_exit"
fi
cache_tmp="${cache_file}.tmp.$$"
trap 'rm -f -- "$cache_tmp" "$failure_tmp"' EXIT
ln -- "$output" "$cache_tmp" 2>/dev/null || cp -- "$output" "$cache_tmp"
mv -f -- "$cache_tmp" "$cache_file"
rm -f -- "$failure_file"
trap - EXIT
rm -f -- "$failure_tmp"
printf 'SCRATCH_CACHE_LEAF FILE=%s\n' "$source"
REMOTE_CACHE_LEAF
}
REMOTE_CACHE_HELPERS
  fi
  printf '%s\n' "$build_command"
} | ssh "${ssh_args[@]}" "$box_host" /bin/bash 2>&1 | capture_build_output
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
elif ((!profile)); then
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
  # Per-module cache-key calculation above intentionally reuses the import
  # walk arrays.  Reconstruct the complete requested environment before the
  # end-of-gate mutation check.
  environment_walk_seen=()
  tracked_dependency_files=()
  for lean_file in "${lean_files[@]}"; do
    collect_environment_imports "$lean_file"
  done
  current_tracked_environment_hash="$(hash_tracked_environment)"
  if [[ "$current_tracked_environment_hash" != "$tracked_environment_hash" ]]; then
    echo "TRACKED_ENVIRONMENT_CHANGED_DURING_VERIFY" >&2
    echo "EXPECTED_SHA256=$tracked_environment_hash CURRENT_SHA256=$current_tracked_environment_hash" >&2
    exit 1
  fi
  for ((i = 0; i < ${#scratch_compile_files[@]}; i++)); do
    current_hash="$(sha256_file "$project_dir/${scratch_compile_files[$i]}")"
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
  echo "GATE_RECEIPT_SHA256=$gate_fingerprint"
  echo "GATE_RECEIPT=$gate_receipt"
fi
