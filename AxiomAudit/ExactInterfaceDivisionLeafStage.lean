import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionLeafStage
import AxiomAudit.Command

open AlgebraicComplexity

/-! Focused trust audit for
`AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionLeafStage`: the leaf-local
bridges from a nonempty whole-constituent laser-volume stage to its packed form, the canonical
one-copy zeroth-power stage, and the corresponding `ExactInterfaceTermDivisionTree.LeafStages`
constructors for a nonempty and for a zero-multiplicity leaf. -/

#assert_axioms WholeConstituentLaserVolumeStage.Packed.ofNonempty
#assert_axioms WholeConstituentLaserVolumeStage.powerZero_restricts_matrixMultiplicationOne
#assert_axioms WholeConstituentLaserVolumeStage.powerZero
#assert_axioms WholeConstituentLaserVolumeStage.Packed.powerZero
#assert_axioms ExactInterfaceTermDivisionTree.LeafStages.ofNonempty
#assert_axioms ExactInterfaceTermDivisionTree.LeafStages.zero
