#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"
mkdir -p build

mode="${1:---full}"
if [[ $# -gt 1 || ( "$mode" != --full && "$mode" != --components ) ]]; then
  printf 'Usage: bash verify.sh [--full|--components]\n' >&2
  exit 2
fi

if [[ -x .toolchain/bin/lake ]]; then
  lake_command=.toolchain/bin/lake
else
  lake_command=lake
fi

python3 scripts/check_audit.py --source-only
"$lake_command" build 2>&1 | tee build/lake-build.txt
python3 scripts/run_axiom_audit.py --lake "$lake_command" --batch-size 256 --jobs 3 --output build/axioms.txt
python3 scripts/check_audit.py build/axioms.txt
"$lake_command" env lean ProofAudit.lean 2>&1 | tee build/proof-dependencies.txt
grep -Fxq 'PROJECT_PROOF_DEPENDENCY_AUDIT_COMPLETE' build/proof-dependencies.txt

if [[ "$mode" == --full ]]; then
  if ! "$lake_command" env lean FullVerification.lean 2>&1 | tee build/full-verification.txt; then
    printf 'FULL VERIFICATION FAILED: a closed proof of Theorem11 is required.\n' >&2
    exit 1
  fi
  python3 scripts/check_audit.py --full-output build/full-verification.txt
fi
