/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymptoticRank
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume

set_option autoImplicit false

/-!
# Whole-constituent stages with a single retained constituent

`MatrixMultiplication/WholeConstituentLaserVolume.lean` stores a finite extraction as a
restriction onto an *indexed direct sum* of equal rectangular tensors.  When the extraction retains
exactly one constituent, that direct sum is its single summand
(`Tensor.Isomorphic.indexedDirectSum_unique`), so the whole stage is one plain exact restriction
onto one matrix-multiplication tensor.  This module packages that degenerate case, together with
the two power laws a client needs to *build* such a restriction out of letterwise ones:

* `Tensor.Restricts.power_matrixMultiplication` — a positive canonical power of a rectangular
  restriction is a rectangular restriction with all three dimensions raised to that power;
* `Tensor.Restricts.powerAdd_matrixMultiplication` — two rectangular restrictions of canonical
  powers of *one* source combine into a rectangular restriction of the summed power, with the three
  dimensions multiplying.

Together they let a client spell a single fine block address of a long tensor power as a word over
finitely many letterwise restrictions, with no partition, no compatibility predicate and no
counting: the copy count is `1` by construction.  The target dimensions and the summed exponent are
taken as *equations* rather than as literal products, so that a caller never has to rewrite under
the dependent `MMSpace` leg family.

This module is candidate-independent: it mentions no particular tensor and no numerical bound.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

section Power

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- A positive canonical power of an exact restriction onto a rectangular tensor is an exact
restriction onto the rectangular tensor with all three dimensions raised to that power.

The zeroth power is excluded for the same reason as in
`Tensor.Isomorphic.power_matrixMultiplication`: it is a pure tensor with one-dimensional legs, and
identifying it with `⟨1,1,1⟩` needs an identification this statement does not carry. -/
theorem Tensor.Restricts.power_matrixMultiplication {T : Tensor3 K V} {m n p : ℕ}
    (h : Restricts T (matrixMultiplication (K := K) m n p)) {k : ℕ} (hk : 0 < k) :
    Restricts (Tensor.power T k)
      (matrixMultiplication (K := K) (m ^ k) (n ^ k) (p ^ k)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  exact (h.power (j + 1)).trans
    (Isomorphic.power_matrixMultiplication (K := K) m n p j).restricts

/-- Two rectangular restrictions of canonical powers of one tensor combine into a rectangular
restriction of the summed power: the exponents add and the three dimensions multiply.

This is the exact-restriction shadow of
`WholeConstituentLaserVolumeStage.powerAdd`, and it is the step that turns a per-letter reading of
a block address into a whole-word reading.  The conclusion's exponent and dimensions are supplied
as equations so that arithmetic normalization happens on `ℕ`, never under `MMSpace`. -/
theorem Tensor.Restricts.powerAdd_matrixMultiplication {T : Tensor3 K V}
    {leftExponent rightExponent exponent : ℕ}
    {m n p m' n' p' M N P : ℕ}
    (hleft : Restricts (Tensor.power T leftExponent)
      (matrixMultiplication (K := K) m n p))
    (hright : Restricts (Tensor.power T rightExponent)
      (matrixMultiplication (K := K) m' n' p'))
    (hexponent : leftExponent + rightExponent = exponent)
    (hM : m * m' = M) (hN : n * n' = N) (hP : p * p' = P) :
    Restricts (Tensor.power T exponent) (matrixMultiplication (K := K) M N P) := by
  subst hexponent
  subst hM
  subst hN
  subst hP
  exact (Tensor.isomorphic_external_power T leftExponent rightExponent).symm.restricts.trans
    ((hleft.external hright).trans
      (Isomorphic.matrixMultiplication_external (K := K) m n p m' n' p').restricts)

end Power

section Stage

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **One exact restriction onto one rectangular tensor is a whole-constituent stage of copy count
`1`.**

The index type is a one-element type in an arbitrary universe, so the stage fits every client
whose stage family is universe-polymorphic in the output index (in particular
`RetainedExtractionValid.of_stageFamily` of the total-weight sequence packaging).  Nothing here is
assumed: `source_restricts` is the supplied restriction composed with the canonical collapse of a
one-summand direct sum. -/
noncomputable def WholeConstituentLaserVolumeStage.ofRestricts
    {source : Tensor3 K V} {xSize ySize zSize : ℕ}
    (h : Restricts source (matrixMultiplication (K := K) xSize ySize zSize)) :
    WholeConstituentLaserVolumeStage.{u, v, z} K source 1 xSize ySize zSize where
  I := PUnit.{z + 1}
  card_I := by simp
  source_restricts :=
    h.trans (Isomorphic.indexedDirectSum_unique (K := K) (ι := PUnit.{z + 1})
      (matrixMultiplication (K := K) xSize ySize zSize)).symm.restricts

end Stage

end AlgebraicComplexity
