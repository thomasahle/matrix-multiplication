import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.MarkedXYPresentPartitionGrouping

open AlgebraicComplexity

/-! Focused trust audit for
`AlgebraicComplexity.MatrixMultiplication.MarkedXYPresentPartitionGrouping`: the support of the
present marked-XY isolated partition, the decomposition of its cardinality as a sum over
occupied Z fibers, and the two restrictions onto grouped and occupied-grouped shared-Z fibers. -/

#assert_axioms PartitionHashEncoding.presentMarkedXYIsolatedPartition_support
#assert_axioms PartitionHashEncoding.card_presentMarkedXYIsolated_eq_sum_occupiedZFiber
#assert_axioms PartitionHashEncoding.restricts_presentMarkedXYIsolated_groupedZFibers
#assert_axioms PartitionHashEncoding.restricts_presentMarkedXYIsolated_occupiedGroupedZFibers
