/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPair112Grouping
import AlgebraicComplexity.Examples.CoppersmithWinograd112Global
import AlgebraicComplexity.Tensor.PositiveWordConstantPower

set_option autoImplicit false

/-!
# Cyclic extraction from the sorted-pair CW `(112)` residual

This module composes the finite algebraic pieces of the exceptional `(1,1,2)` construction.  A
complete power of the two-address sorted-pair residual first restricts factorwise to the
four-address CW `(112)` partition.  Constant positive-word coherence identifies that product with
the canonical tensor power.  Applying the restriction simultaneously to the three cyclic
orientations then reaches the existing global pipeline: X/Y isolation, grouping by one shared Z
word, retyping each group as a C-tensor, and the generic C-tensor-to-matrix-multiplication
degeneration.

This is a relation-explicit finite formulation of the grouped `(112)` argument in
[CoppersmithWinograd1990, pp. 270--272], following the theorem-oriented transcription at
`papers/notes/MMult1987.tex:226-259`.  In particular, the C-tensor step is expressed through a
polynomial degeneration rather than an unproved numerical ``value'' law.  The theorem is an
explanatory structural regression only: it contains no entropy estimate, survivor count,
optimization, or exponent conclusion, and therefore does not claim the sharp CW endpoint.  Its
final imported stage is the historical per-orientation shared-Z route; it is not the separate
64-address cyclic typed-leaf extraction used by the sharp modern value client, described separately
at `papers/notes/MMult1987.tex:261-285`.

## Reference

- [CoppersmithWinograd1990] Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via
  Arithmetic Progressions*.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The cyclic product of a complete sorted-pair residual power polynomially degenerates to the
square matrix-multiplication families obtained from the shared-Z C-tensor construction.

In human-readable terms, set `n = cw112TypeDepth L G`.  The source consists of the complete
`(n+1)`-letter residual product and its two cyclic leg rotations.  No residual Z address is
discarded before this cyclic product is formed.  The target has one outer summand for each occupied
shared-Z word and one inner square matrix-multiplication summand for each minimum-weight
antidiagonal address of that word's C-tensor.

Proof sketch: use `cwSortedPair112ResidualPositivePower_restricts_wordTensor` to restrict the
complete residual product to the constant positive-word product of four-address CW `(112)`
partitions.  The generic `Isomorphic.positiveWordTensor_const_power` turns this into the canonical
power used by `cw112PowerCyclicProduct`.  Tensor that restriction with its two cyclic rotations,
promote the resulting exact restriction to a polynomial degeneration, and compose with
`cw112PowerCyclicProduct_degenerates_squareFamilies`, whose proof performs X/Y isolation, the
genuine shared-Z grouping, and the generic C-tensor degeneration. -/
theorem cwSortedPair112ResidualCyclicPower_degenerates_squareFamilies
    (K : Type u) [CommRing K] (q L G : ℕ)
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    let residualPower :=
      (((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).withSupport
        cwSortedPair112ResidualSupport).positivePower
          (cw112TypeDepth L G)).realize)
    PolynomialDegenerates
      (Tensor.external
        (Tensor.external residualPower (Tensor.permute cycle residualPower))
        (Tensor.permute cycle.symm residualPower))
      (cw112FiniteLeafSquareFamilies K q L G B hB seed) := by
  dsimp only
  let n := cw112TypeDepth L G
  let residualPower :=
    (((((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).withSupport
      cwSortedPair112ResidualSupport).positivePower n).realize)
  let targetFamily := LegModuleFamily.of.{u, u} (K := K)
    (PartitionedSpace K (CW112PartitionBlockSpace K q))
  let targetTensor := (cw112PartitionedTensor K q).realize
  let groupedWord :=
    (positiveWordBlockAddressEquiv (fun _c : Leg ↦ Unit) n).symm
      (cwSortedPair112ResidualGroupedTarget n)
  change PolynomialDegenerates
    (Tensor.external
      (Tensor.external residualPower (Tensor.permute cycle residualPower))
      (Tensor.permute cycle.symm residualPower))
    (cw112FiniteLeafSquareFamilies K q L G B hB seed)
  have hword : Restricts residualPower
      (positiveWordTensor
        (fun _address : BlockAddress (fun _c : Leg ↦ Unit) ↦ targetFamily)
        (fun _address ↦ targetTensor) n groupedWord) := by
    simpa only [residualPower, targetFamily, targetTensor, n, groupedWord] using
      (cwSortedPair112ResidualPositivePower_restricts_wordTensor
        K q (cw112TypeDepth L G))
  have hconstant : Isomorphic
      (positiveWordTensor
        (fun _address : BlockAddress (fun _c : Leg ↦ Unit) ↦ targetFamily)
        (fun _address ↦ targetTensor) n groupedWord)
      (Tensor.power targetTensor (n + 1)) :=
    Tensor.Isomorphic.positiveWordTensor_const_power
      targetFamily targetTensor n groupedWord
  have hpower : Restricts residualPower (Tensor.power targetTensor (n + 1)) :=
    hword.trans hconstant.restricts
  have hcyclic : Restricts
      (Tensor.external
        (Tensor.external residualPower (Tensor.permute cycle residualPower))
        (Tensor.permute cycle.symm residualPower))
      (cw112PowerCyclicProduct K q L G) := by
    simpa only [cw112PowerCyclicProduct, targetTensor, n] using
      ((hpower.external (hpower.permute cycle)).external
        (hpower.permute cycle.symm))
  exact (Tensor.PolynomialDegenerates.of_restricts hcyclic).trans
    (cw112PowerCyclicProduct_degenerates_squareFamilies
      K q L G B hB seed)

end AlgebraicComplexity.Examples
