/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PartitionedSelectStructure

/-! # Axiom audit for block selection through permutation and external product

The two projection lemmas for inverse permutation transport of a product block address, and the
two structural identities: permuting a cut certificate cuts the permuted certificate, and the
external product of two cut certificates is a cut of the external product.

These formalize the commutation/restriction bridge `[duan2023faster]` needs at
`papers/sources/2210.10173/second_power_appendix.tex:37` (inside the proof of
`lem:non-rot-values` (d), `:26-45`, especially `:31-37`), where the paper cuts by the
marginals and only then forms `sym_3`; the general reason is `global_value.tex:98-121`,
Step 4 at `:104` and the implicit symmetrization at `:121`.  The Lean statements themselves
are general partitioned-tensor facts, not published claims. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Tensor.permuteBlockAddress_symm_fst
#assert_axioms AlgebraicComplexity.Tensor.permuteBlockAddress_symm_snd
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.permute_select
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.external_select
