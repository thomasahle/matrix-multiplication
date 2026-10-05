/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.AsymptoticRankCalculus
import AlgebraicComplexity.Tensor.IndexedProduct
import AlgebraicComplexity.MatrixMultiplication.IndexedTauWeight
import AlgebraicComplexity.MatrixMultiplication.SixSymmetrizedValue
import AlgebraicComplexity.MatrixMultiplication.SymThreeCycleInvariance

set_option autoImplicit false

/-!
# How `sym₆` distributes: over a direct sum of equal summands, and over a product

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `[DuanWuZhou2022]` never hashes a
symmetrized tensor.
Its section 6 hashes a *plain* power `T^{⊗n}`, degenerates it onto a direct sum of `m` copies of
**one** leaf, and only then --- `global_value.tex`:120, *"one more implicit step, symmetrization,
which is hidden under the notation of `V^(6)`"* --- applies `sym₆`, once, to the direct sum.  Two
distribution laws carry the value across that last step, and this module supplies both.

## The two laws

* **Over a direct sum of equal summands.**  `Isomorphic.symSix_indexedDirectSum_uniform`:
  `sym₆(⊕_{i ∈ ι} L) ≅ ⊕_{ι⁶} sym₆(L)`.  Rotation and swapping distribute over a direct sum
  (`Tensor.permute_indexedDirectSum`, an *equality*) and the external product distributes
  pairwise (`Isomorphic.external_indexedDirectSum`), so each of the six factors of `sym₆` splits
  independently.  Because the summands are all the same `L`, *every* one of the `|ι|⁶` cross terms
  --- not only the `|ι|` diagonal ones --- is a copy of `sym₆(L)`.

  This is the step that reconciles the two copy counts.  A construction that retains `m` copies of
  a uniform leaf yields `m⁶` copies after symmetrization, so a copy budget stated per *oriented*
  letter, `rate^(6n)`, is met by a hash that only has to produce `rate^n` copies --- which is what
  the paper's `N_retain` (`global_value.tex`:140, all exponents in `n`) delivers.  No six-orientation
  block family, and no independently varying orientations, are needed to reach the `6n` exponent.

* **Over a product.**  `Isomorphic.symSix_external`: `sym₆(A ⊗ B) ≅ sym₆(A) ⊗ sym₆(B)`, and
  `Isomorphic.symSix_power_positive`: `sym₆(T^{⊗(n+1)}) ≅ sym₆(T)^{⊗(n+1)}`.  Together they lock
  the six orientations *diagonally* across a product of powers
  `⊗_s T_s^{⊗ e_s`}`: the six copies of each factor carry the same index with the same exponent,
  so a per-component six-symmetrized value applies to each factor separately and no relation
  between different components' orientations ever has to be tracked.

## Overlap with `MatrixMultiplication/SymSixUniformLeaf.lean`

That module (another lane, concurrent) states the same uniform-direct-sum distribution.  Two
differences, both deliberate here:

* its `sym₆` form is a `Restricts`, on the stated ground that `Tensor.permute` *"has no
  `Isomorphic` companion in the tree"*.  It has one --- `Tensor.Isomorphic.permute_legs`,
  `Tensor/Restriction.lean`:108 --- so `Isomorphic.symSix_indexedDirectSum_uniform` below is the
  same statement without the weakening, and a client that needs only a restriction takes
  `.restricts`;
* the names here are `…_uniform`, and the six-fold index is written inline rather than abbreviated,
  so that the two modules cannot clash on a declaration name or make `SymSixIndex` ambiguous under
  `open Tensor` while the duplication is being merged.

`MERGE (janitor):` keep one copy of the uniform-direct-sum law --- the `Isomorphic` one --- and one
copy of the index abbreviation; `SymSixUniformLeaf`'s `Restricts` functoriality and its
`power_symSix` stage bridge are not duplicated here and should survive.

## Why this is stated here and not for a partitioned tensor

Nothing below mentions a partition, a support, a block label or a distribution: the laws are about
`Tensor.external`, `Tensor.permute` and `Tensor.indexedDirectSum` only.  A partitioned client
reaches them through the realization, and a laser client through the leaf it degenerates onto.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6 (`global_value.tex`), and section 2.1 for `sym₃`/`sym₆`.
-/

namespace AlgebraicComplexity.Tensor

universe u v w z t

/-! ## Congruence -/

section Congr

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type z} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- **`sym₆` respects legwise isomorphism.**

The `sym₃` half is the committed `AlgebraicComplexity.Isomorphic.symThree_congr`
(`MatrixMultiplication/SymThreeCycleInvariance.lean`:98); only the outer swapped factor is added
here. -/
theorem Isomorphic.symSix_congr {T : Tensor3 K V} {S : Tensor3 K W} (h : Isomorphic T S) :
    Isomorphic (symSix K T) (symSix K S) :=
  (AlgebraicComplexity.Isomorphic.symThree_congr h).external
    ((AlgebraicComplexity.Isomorphic.symThree_congr h).permute_legs Tensor.swapXY)

end Congr

/-! ## Distribution over a direct sum of equal summands -/

section DirectSum

variable {K : Type u} [CommSemiring K]
variable {ι : Type w} [Fintype ι]
variable {U : Leg → Type v} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]

/-- **`sym₃` of a direct sum of equal summands.**

`sym₃(⊕_{i ∈ ι} L) ≅ ⊕_{(ι × ι) × ι} sym₃(L)`: the three factors split independently and every
cross term is a copy of `sym₃(L)`, because all the summands are the same `L`. -/
theorem Isomorphic.symThree_indexedDirectSum_uniform (L : Tensor3 K U) :
    Isomorphic (symThree K (Tensor.indexedDirectSum (V := fun _ : ι ↦ U) (fun _ ↦ L)))
      (Tensor.indexedDirectSum (fun _ : (ι × ι) × ι ↦ symThree K L)) := by
  unfold symThree
  rw [Tensor.permute_indexedDirectSum, Tensor.permute_indexedDirectSum]
  exact Isomorphic.external3_indexedDirectSum _ _ _

/-- **`sym₆` of a direct sum of equal summands.**

`sym₆(⊕_{i ∈ ι} L) ≅ ⊕_{SymSixIndex ι} sym₆(L)`, and `Fintype.card (SymSixIndex ι) = |ι|⁶`.

This is the law `[DuanWuZhou2022]` section 6 uses implicitly when it applies `sym₆` to
`(𝒯*)^{⊕m'}` at the very end: `m'` retained copies of one uniform leaf become `m'⁶` copies of the
symmetrized leaf, which is exactly the ratio between a copy budget stated per position and one
stated per oriented letter. -/
theorem Isomorphic.symSix_indexedDirectSum_uniform (L : Tensor3 K U) :
    Isomorphic (symSix K (Tensor.indexedDirectSum (V := fun _ : ι ↦ U) (fun _ ↦ L)))
      (Tensor.indexedDirectSum (fun _ : ((ι × ι) × ι) × ((ι × ι) × ι) ↦ symSix K L)) := by
  have h3 := Isomorphic.symThree_indexedDirectSum_uniform (K := K) (ι := ι) L
  unfold symSix
  refine (h3.external (h3.permute_legs Tensor.swapXY)).trans ?_
  rw [Tensor.permute_indexedDirectSum]
  exact Isomorphic.external_indexedDirectSum _ _

end DirectSum

/-! ## The weight corollary -/

section Weight

variable {K : Type u} [CommSemiring K]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {U : Leg → Type v} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]

/-- **A weight on the symmetrized leaf gives `|ι|⁶` times that weight on the symmetrized direct
sum.**

The form a laser endpoint consumes: a construction that produces `m` copies of a uniform leaf `L`,
together with one `tau`-weight for `sym₆(L)`, already carries `m⁶ · w` on `sym₆` of the whole
direct sum --- no per-copy distinctness, and no six-orientation bookkeeping. -/
theorem HasTauWeight.symSix_indexedDirectSum_uniform {τ w : ℝ} {L : Tensor3 K U}
    (h : HasTauWeight K (symSix K L) τ w) :
    HasTauWeight K
      (symSix K (Tensor.indexedDirectSum (V := fun _ : ι ↦ U) (fun _ ↦ L))) τ
      ((Fintype.card ι : ℝ) ^ 6 * w) := by
  have hsum : HasTauWeight K
      (Tensor.indexedDirectSum (fun _ : ((ι × ι) × ι) × ((ι × ι) × ι) ↦ symSix K L)) τ
      ((Fintype.card (((ι × ι) × ι) × ((ι × ι) × ι)) : ℝ) * w) :=
    HasTauWeight.indexedDirectSum_of_forall fun _ ↦ h
  have hcard : Fintype.card (((ι × ι) × ι) × ((ι × ι) × ι)) = Fintype.card ι ^ 6 := by
    simp only [Fintype.card_prod]
    ring
  rw [hcard] at hsum
  push_cast at hsum
  exact HasTauWeight.of_restricts
    (Isomorphic.symSix_indexedDirectSum_uniform (K := K) (ι := ι) L).restricts hsum

end Weight

/-! ## Distribution over a product: the diagonal locking -/

section Product

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type z} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- **`sym₃` of a product is the product of the `sym₃`s.**

`(A ⊗ B)^rot = A^rot ⊗ B^rot` on the nose (`Tensor.permute_external`), so `sym₃(A ⊗ B)` and
`sym₃(A) ⊗ sym₃(B)` differ only by a perfect shuffle of the six factors --- two middle-four
interchanges. -/
theorem Isomorphic.symThree_external (A : Tensor3 K V) (B : Tensor3 K W) :
    Isomorphic (symThree K (Tensor.external A B))
      (Tensor.external (symThree K A) (symThree K B)) := by
  unfold symThree
  rw [Tensor.permute_external, Tensor.permute_external]
  refine ((Isomorphic.external_interchange A B (Tensor.permute cycle A)
    (Tensor.permute cycle B)).external (Isomorphic.refl _)).trans ?_
  exact Isomorphic.external_interchange _ _ _ _

/-- **`sym₆` of a product is the product of the `sym₆`s.**

The diagonal locking: in a product `⊗_s T_s` the six orientations of each factor stay attached to
that factor, so a per-factor six-symmetrized value applies factorwise and no relation between
different factors' orientations arises. -/
theorem Isomorphic.symSix_external (A : Tensor3 K V) (B : Tensor3 K W) :
    Isomorphic (symSix K (Tensor.external A B))
      (Tensor.external (symSix K A) (symSix K B)) := by
  have h3 := Isomorphic.symThree_external (K := K) A B
  unfold symSix
  refine (h3.external (h3.permute_legs Tensor.swapXY)).trans ?_
  rw [Tensor.permute_external]
  exact Isomorphic.external_interchange _ _ _ _

/-- **`sym₆` of a positive power is the power of the `sym₆`.**

`sym₆(T^{⊗(n+1)}) ≅ sym₆(T)^{⊗(n+1)}`, by peeling one factor and `Isomorphic.symSix_external`.
Stated at positive exponents because that is the shape a leaf `⊗_s T_s^{⊗ e_s}` presents and it
avoids the zeroth-power unit. -/
theorem Isomorphic.symSix_power_positive (T : Tensor3 K V) :
    ∀ n : ℕ, Isomorphic (symSix K (Tensor.power T (n + 1)))
      (Tensor.power (symSix K T) (n + 1))
  | 0 =>
      ((Isomorphic.power_one T).symSix_congr).trans (Isomorphic.power_one (symSix K T)).symm
  | n + 1 => by
      refine ((isomorphic_external_power T (n + 1) 1).symm.symSix_congr).trans ?_
      refine (Isomorphic.symSix_external _ _).trans ?_
      refine ((Isomorphic.symSix_power_positive T n).external
        ((Isomorphic.power_one T).symSix_congr)).trans ?_
      refine ((Isomorphic.refl _).external (Isomorphic.power_one (symSix K T)).symm).trans ?_
      exact isomorphic_external_power (symSix K T) (n + 1) 1

/-- **The two-factor product-of-powers form**, the shape a laser leaf
`⊗_s T_s^{⊗ e_s}` is built from: iterating this and `symSix_external` locks the orientations of
every factor of such a product to that factor. -/
theorem Isomorphic.symSix_external_power_positive (A : Tensor3 K V) (B : Tensor3 K W)
    (a b : ℕ) :
    Isomorphic (symSix K (Tensor.external (Tensor.power A (a + 1)) (Tensor.power B (b + 1))))
      (Tensor.external (Tensor.power (symSix K A) (a + 1))
        (Tensor.power (symSix K B) (b + 1))) :=
  (Isomorphic.symSix_external _ _).trans
    ((Isomorphic.symSix_power_positive A a).external (Isomorphic.symSix_power_positive B b))

end Product

end AlgebraicComplexity.Tensor
