import MatrixMultiplication
import MatrixMultiplication.Generated.ParentGainData
import MatrixMultiplication.Generated.LevelFourFeasibilityData
import MatrixMultiplication.Generated.SimplifiedCW112Leaves
import MatrixMultiplication.TotalQuotientRetainedCompressionSeam
import MatrixMultiplication.SimplifiedRetainedCompressionSeam
import MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedCertificate
import MatrixMultiplication.TotalQuotientExponentLevelFourCertificate

/-!
# Exact certificate checker

This opt-in umbrella imports the generated exact parent-gain tables and their kernel-checked
arithmetic proofs, the exact level-four feasibility tables, and the theorem interpreting every
positive generated level-two entry as a rational CW `112` typed leaf.  It also checks the compact
67-record sufficient statistic and directed numerical floor for the total-quotient level-two
recurrence, and the two retained-exponent compression seams — the total-weight quotient's
(`e7987…`) and the simplified certificate's (`eab2c7…`, the volume-only `2.36999` payload).
The compact level-four checker contributes all eighteen selected-parent regional branch-floor
inequalities and rewrites its cached rows to the recurrence reconstructed from the total-weight
primary tables.
Keeping these modules separate from `MatrixMultiplication` prevents the intentionally heavy
generated builds from slowing ordinary library work.
-/
