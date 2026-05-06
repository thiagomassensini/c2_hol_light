#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "$0")" && pwd)"
source "$script_dir/hol_light_env.sh"

log="${TMPDIR:-/tmp}/hol_c2_public_api.$$.log"
run_hol_c2_loader "$script_dir" "load_c2_public_api.ml" "hol-c2-public-api-ok" "$log"