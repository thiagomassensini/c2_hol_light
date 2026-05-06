#!/usr/bin/env bash
set -euo pipefail

list_hol_light_dirs() {
  local script_dir repo_root candidate
  script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  repo_root="$(cd "$script_dir/.." && pwd)"

  for candidate in \
    "${HOL_LIGHT_DIR:-}" \
    "$repo_root/hol-light" \
    "/home/thlinux/numerico/formal/hol-light" \
    "/home/thlinux/numerico/formal/hol-light (Cópia)" \
    "/home/thlinux/backup_numerico/formal/hol-light"
  do
    if [[ -n "$candidate" && -x "$candidate/ocaml-hol" && -f "$candidate/hol.ml" ]]; then
      printf '%s\n' "$candidate"
    fi
  done
}

resolve_hol_light_dir() {
  local candidate

  while IFS= read -r candidate; do
    if [[ -n "$candidate" ]]; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done < <(list_hol_light_dirs)

  echo "Could not locate a HOL Light checkout. Set HOL_LIGHT_DIR or place hol-light beside the repo." >&2
  return 1
}

run_hol_c2_loader() {
  if [[ $# -ne 4 ]]; then
    echo "usage: run_hol_c2_loader <hol_c2_dir> <loader> <marker> <log>" >&2
    return 1
  fi

  local hol_c2_dir="$1"
  local loader="$2"
  local marker="$3"
  local log="$4"
  local hol_light_dir temp_loader attempt_log found_candidate

  temp_loader="$(mktemp "${TMPDIR:-/tmp}/hol_c2_loader.XXXXXX.ml")"
  attempt_log="$(mktemp "${TMPDIR:-/tmp}/hol_c2_loader.XXXXXX.log")"
  found_candidate=0

  cleanup_hol_c2_loader() {
    rm -f "$temp_loader"
    rm -f "$attempt_log"
  }

  trap cleanup_hol_c2_loader RETURN

  sed "s#\.\./hol_c2/#$hol_c2_dir/#g" "$hol_c2_dir/$loader" > "$temp_loader"

  while IFS= read -r hol_light_dir; do
    [[ -n "$hol_light_dir" ]] || continue
    found_candidate=1
    : > "$attempt_log"

    if ! (cd "$hol_light_dir" && ./ocaml-hol < "$temp_loader" | tee "$attempt_log"); then
      true
    fi

    if ! grep -E "Error in included file|Exception:" "$attempt_log" >/dev/null &&
       grep -q "$marker" "$attempt_log"; then
      cp "$attempt_log" "$log"
      return 0
    fi
  done < <(list_hol_light_dirs)

  if [[ "$found_candidate" -eq 0 ]]; then
    echo "Could not locate a HOL Light checkout. Set HOL_LIGHT_DIR or place hol-light beside the repo." >&2
    return 1
  fi

  cp "$attempt_log" "$log"
  return 1
}