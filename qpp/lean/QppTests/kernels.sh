#!/usr/bin/env bash
# Replays declarations of a built module of qpp/lean in the three kernels of the toolchain, as `lake comparator`
# runs them: Lean's own (leanchecker --from-export), NanoDa (nanoda_bin, with its Nat extension) and con-ron, on
# one export (leanexport). Prints the wall time of each; fails if any kernel rejects or an axiom other than
# propext, Classical.choice and Quot.sound is used.
#
# Usage (from qpp/lean, after `lake build MODULE`): QppTests/kernels.sh MODULE [DECL ...]
set -euo pipefail
module=$1
shift
prefix=$(lake env lean --print-prefix)
bin="$prefix/bin"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
export_file="$tmp/export.ndjson"

seconds() { local t0=$1; echo "$(( $(date +%s%N) - t0 ))" | awk '{printf "%.2f", $1 / 1e9}'; }

t0=$(date +%s%N)
if [ $# -gt 0 ]; then
  lake env "$bin/leanexport" "$module" -- "$@" > "$export_file"
else
  lake env "$bin/leanexport" "$module" > "$export_file"
fi
echo "export: $(seconds "$t0") s, $(wc -l < "$export_file") records, $(du -h "$export_file" | cut -f1)"

cat > "$tmp/nanoda.json" <<EOF
{"use_stdin": false, "export_file_path": "$export_file",
 "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
 "unpermitted_axiom_hard_error": true, "num_threads": 4, "nat_extension": true, "string_extension": true}
EOF

status=0
run() {
  local name=$1
  shift
  local t0
  t0=$(date +%s%N)
  if "$@" > "$tmp/$name.log" 2>&1; then
    echo "$name: accepted, $(seconds "$t0") s"
  else
    echo "$name: REJECTED after $(seconds "$t0") s"
    tail -20 "$tmp/$name.log"
    status=1
  fi
}
run lean "$bin/leanchecker" --silent --from-export "$export_file"
run nanoda "$bin/nanoda_bin" "$tmp/nanoda.json"
run con-ron "$bin/con-ron" --jobs=2 "$export_file"
if grep -q '"axiom"' "$export_file"; then
  axioms=$(grep -o '"axiom":{[^}]*"name":[0-9]*' "$export_file" | wc -l)
  echo "axiom records in the export: $axioms (only the declarations used are replayed)"
fi
exit $status
