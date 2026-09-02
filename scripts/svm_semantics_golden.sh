#!/usr/bin/env bash
# svm-sem-002: build the E2 SemanticsBridge golden subset (Counter + Window + named parse).
# Failures surface as Lean theorem errors that name the program/scenario.
set -euo pipefail
cd "$(dirname "$0")/.."
echo "svm-sem-002: lake build Tests.SemanticsSpec"
exec lake build Tests.SemanticsSpec
