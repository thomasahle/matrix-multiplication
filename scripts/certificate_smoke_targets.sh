#!/usr/bin/env bash
# Print the Lake targets of the certificate smoke check, on one line.
#
# The full certificate tier (`MatrixMultiplicationCertificate AxiomAuditCertificate`) is about
# 11,000 generated modules, and roughly 10,500 of them are the level-four analytic tables
# (`MatrixMultiplication/Generated/TotalQuotientExponentLevelFourAnalytic*`).  On a 2-core hosted
# runner that is about 14 hours, more than a GitHub job may run, so CI builds the full tier only on
# a manual run.  This script selects a slice that fits in a normal CI job:
#
#   * every `AxiomAuditCertificate.*` audit except the six whose import closure reaches the
#     analytic tables or several hundred other generated modules (listed in HEAVY below);
#   * two modules from the analytic family itself, so that a break in what those tables import
#     (as happened in the split of `DyadicEntropyForm`) is caught.
#
# The slice is about 330 certificate-only modules.  It reads only tracked files.
set -euo pipefail
cd "$(dirname "$0")/.."

HEAVY='^AxiomAuditCertificate\.(TotalQuotientExponentLevelFourAnalytic|Census|TotalQuotientExponentLevelFourValidity|CensusRoots|CertifiedLevelFourOccurrenceExtractionClients|CertifiedLevelFourOccurrenceTargets)$'

SAMPLES=(
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk0Parent0Raw
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk3Parent1Raw
)

{
  git ls-files 'AxiomAuditCertificate/*.lean' |
    sed -e 's/\.lean$//' -e 's#/#.#g' |
    grep -Ev "$HEAVY"
  printf '%s\n' "${SAMPLES[@]}"
} | sort -u | tr '\n' ' ' | sed 's/ $//'
echo
