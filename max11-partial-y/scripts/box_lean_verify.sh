#!/usr/bin/env bash
# Sync this project to the dedicated Lean box and run a fail-closed build.
set -euo pipefail

box_host="${BOX_LEAN_HOST:-ubuntu@54.81.66.156}"
box_key="${BOX_LEAN_KEY:-/Users/dc/.ssh/claude-cli.pem}"
box_dir="${BOX_LEAN_DIR:-/home/ubuntu/jc2-lean/max11-partial-y}"
run_axioms=0
full_build=0
verbose="${BOX_LEAN_VERBOSE:-0}"
lean_files=()
modules=()

usage() {
  echo "usage: $0 [--full | --file File.lean [--file File.lean ...] | LeanModule ...] [--axioms]" >&2
  echo "  --file: isolated scratch/one-file verification" >&2
  echo "  LeanModule ... --axioms: persistent canonical build and full axiom audit" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --full) full_build=1 ;;
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
[[ -r "$box_key" ]] || {
  echo "missing SSH key: $box_key" >&2
  exit 2
}

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
ssh_args=(-i "$box_key" -o BatchMode=yes -o StrictHostKeyChecking=no)
rsync_shell="ssh -i $box_key -o BatchMode=yes -o StrictHostKeyChecking=no"
remote_work_dir="$box_dir"
cleanup_remote=0
local_log=""
axiom_log=""
canonical_lock_dir=""
canonical_lock_acquired=0

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
fi

scratch_compile_files=()
source_hashes=()
scratch_cache_keys=()
tracked_environment_hash=""
if ((${#lean_files[@]})); then
  hash_tracked_environment() {
    (
      cd "$project_dir"
      while IFS= read -r -d '' tracked_file; do
        printf '%s\0' "$tracked_file"
        LC_ALL=C shasum -a 256 "$tracked_file"
      done < <(git ls-files -z -- '*.lean' lean-toolchain lakefile.toml lake-manifest.json)
    ) | LC_ALL=C shasum -a 256 | awk '{print $1}'
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
  done
  for source in "${scratch_compile_files[@]}"; do
    source_hashes+=("$(LC_ALL=C shasum -a 256 "$project_dir/$source" | awk '{print $1}')")
  done
  tracked_environment_hash="$(hash_tracked_environment)"
  cache_state="$tracked_environment_hash"
  for ((i = 0; i < ${#scratch_compile_files[@]}; i++)); do
    cache_state="$(printf '%s\n%s\n%s\n' \
      "$cache_state" "${scratch_compile_files[$i]}" "${source_hashes[$i]}" \
      | LC_ALL=C shasum -a 256 | awk '{print $1}')"
    scratch_cache_keys+=("$cache_state")
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
ssh "${ssh_args[@]}" "$box_host" \
  "cd '$remote_work_dir' && export PATH=/home/ubuntu/.elan/bin:\$PATH && $build_command" \
  >"$local_log" 2>&1
build_exit=$?
set -e
error_count="$(grep -c 'error:' "$local_log" || true)"
sorry_count="$(grep -c 'sorryAx' "$local_log" || true)"
echo "BUILD_EXIT=$build_exit ERROR_COUNT=$error_count SORRYAX_COUNT=$sorry_count"
if ((build_exit != 0 || error_count != 0 || sorry_count != 0)); then
  if ! grep -n -B 2 -A 8 -E 'error:|sorryAx' "$local_log"; then
    tail -n 80 "$local_log"
  fi
  exit 1
fi
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
  axiom_error_count="$(grep -c 'error:' "$axiom_log" || true)"
  axiom_sorry_count="$(grep -c 'sorryAx' "$axiom_log" || true)"
  echo "AXIOM_EXIT=$axiom_exit ERROR_COUNT=$axiom_error_count SORRYAX_COUNT=$axiom_sorry_count"
  if ((axiom_exit != 0 || axiom_error_count != 0 || axiom_sorry_count != 0)); then
    if ! grep -n -B 2 -A 8 -E 'error:|sorryAx' "$axiom_log"; then
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
fi
