#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "$0")" && pwd)"
source "$script_dir/hol_light_env.sh"

log="${TMPDIR:-/tmp}/hol_c2_branch_sigma.$$.log"
run_hol_c2_loader "$script_dir" "load_c2_branch_sigma.ml" "hol-c2-branch-sigma-ok" "$log"
