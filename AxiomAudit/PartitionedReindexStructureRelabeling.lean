import AlgebraicComplexity.Tensor.PartitionedReindexStructureRelabeling
import AxiomAudit.Command

/-!
# Axiom audit for partitioned-reindex structure relabeling

The assertions below audit the inverse block transport, exact reindex cancellation, and public
pullback and pushforward constructors together with their exposed part-equivalence conjugation
laws.
-/

set_option autoImplicit false

open AlgebraicComplexity Tensor

#assert_axioms reindexSymmBlockEquiv
#assert_axioms PartitionedTensor.reindex_symm
#assert_axioms PartitionedTensor.StructureRelabeling.ofReindexBlockEquiv
#assert_axioms PartitionedTensor.StructureRelabeling.ofReindex
#assert_axioms PartitionedTensor.StructureRelabeling.ofReindex_partEquiv
#assert_axioms PartitionedTensor.StructureRelabeling.toReindex
#assert_axioms PartitionedTensor.StructureRelabeling.toReindex_partEquiv
