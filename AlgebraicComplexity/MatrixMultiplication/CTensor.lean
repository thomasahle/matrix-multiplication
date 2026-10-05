/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CTensorCore
import AlgebraicComplexity.Tensor.PartitionedDirectSum
import AlgebraicComplexity.Tensor.PartitionedMonomial
import AlgebraicComplexity.Tensor.PartitionedPermutation
import AlgebraicComplexity.Tensor.PartitionedProduct
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cyclic C-tensors and the matrix-to-scalar degeneration

A C-tensor is a family of constituents with independent X and Y blocks but one shared Z block.
Coppersmith and Winograd recover the lost third-leg independence by externally multiplying three
cyclic orientations.  The resulting support is indexed by triples `i,j,k`; its leg labels remember
the pairs `(i,k)`, `(i,j)`, and `(j,k)`.

This file formalizes the reusable finite algebraic core of that argument.  A nonnegative
block-monomial weighting selects the antidiagonal `i + j = k`.  It is injective on every leg and
the selected realization restricts to a genuine indexed direct sum of constituent products.  The
stronger division-free cardinality estimate `h² ≤ 2|A|` and its finite-family form live in the
separate leaf `CTensorCounting.lean`, so counting changes do not invalidate this semantic core.
No Coppersmith--Winograd constants or asymptotic estimates occur here.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

namespace CTensor

/-- Block labels after taking the product of the original C-tensor and its two nontrivial cyclic
orientations. -/
abbrev TripleBlockIndex (h : ℕ) : Leg → Type :=
  ProductBlockIndex
    (ProductBlockIndex (BlockIndex h) (PermutedBlockIndex cycle (BlockIndex h)))
    (PermutedBlockIndex cycle.symm (BlockIndex h))

/-- The full block address associated with the three source constituent indices `i,j,k`. -/
def tripleAddress {h : ℕ} (i j k : Fin h) : BlockAddress (TripleBlockIndex h) :=
  blockAddressProductEquiv
    (blockAddressProductEquiv (address i, permuteBlockAddress cycle (address j)),
      permuteBlockAddress cycle.symm (address k))

/-- On X, a cyclic triple address records the pair `(i,k)`; the middle cyclic factor contributes
only its shared label. -/
@[simp] theorem tripleAddress_X {h : ℕ} (i j k : Fin h) :
    tripleAddress i j k .X = ((i, ()), k) := rfl

/-- On Y, a cyclic triple address records the pair `(i,j)`; the final cyclic factor contributes
only its shared label. -/
@[simp] theorem tripleAddress_Y {h : ℕ} (i j k : Fin h) :
    tripleAddress i j k .Y = ((i, j), ()) := rfl

/-- On Z, a cyclic triple address records the pair `(j,k)`; the original factor contributes only
its shared label. -/
@[simp] theorem tripleAddress_Z {h : ℕ} (i j k : Fin h) :
    tripleAddress i j k .Z = (((), j), k) := rfl

/-- The three-fold cyclic product of a partitioned C-tensor. -/
noncomputable def cyclicTriple
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :=
  ((partitioned T).external ((partitioned T).permute cycle)).external
    ((partitioned T).permute cycle.symm)

/-- The ordinary tensor obtained by externally multiplying a C-tensor realization with its two
nontrivial cyclic orientations. -/
noncomputable def cyclicTensor
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :=
  Tensor.external
    (Tensor.external (partitioned T).realize
      (Tensor.permute cycle (partitioned T).realize))
    (Tensor.permute cycle.symm (partitioned T).realize)

/-- The ordinary cyclic tensor is canonically isomorphic to the realization of the structured
cyclic-triple partition.

Proof sketch: realization commutes with each leg permutation and with each partitioned external
product.  Apply those two functoriality laws first to the left pair, then to its product with the
third cyclic orientation. -/
theorem cyclicTensor_isomorphic_cyclicTriple
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    Isomorphic (cyclicTensor T) (cyclicTriple T).realize := by
  let P := partitioned T
  have hleft : Isomorphic
      (Tensor.external P.realize (Tensor.permute cycle P.realize))
      (P.external (P.permute cycle)).realize :=
    (Isomorphic.external (Isomorphic.refl P.realize)
      (Isomorphic.partitionedPermute P cycle)).trans
      (Isomorphic.partitionedExternal P (P.permute cycle))
  exact
    (Isomorphic.external hleft (Isomorphic.partitionedPermute P cycle.symm)).trans
      (Isomorphic.partitionedExternal (P.external (P.permute cycle))
        (P.permute cycle.symm))

/-- Every supported address of the cyclic triple comes from three source constituent indices. -/
theorem mem_cyclicTriple_support_iff
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z))
    (s : BlockAddress (TripleBlockIndex h)) :
    s ∈ (cyclicTriple T).support ↔
      ∃ i j k : Fin h, tripleAddress i j k = s := by
  classical
  simp only [cyclicTriple, PartitionedTensor.mem_external_support,
    PartitionedTensor.mem_permute_support]
  constructor
  · rintro ⟨⟨hi, hj⟩, hk⟩
    rcases (mem_support_iff _).1 hi with ⟨i, hi⟩
    rcases (mem_support_iff _).1 hj with ⟨j, hj⟩
    rcases (mem_support_iff _).1 hk with ⟨k, hk⟩
    have hjForward : permuteBlockAddress cycle (address j) = fun c ↦ (s c).1.2 := by
      have h := congrArg (permuteBlockAddress cycle) hj
      simpa using h
    have hkForward : permuteBlockAddress cycle.symm (address k) = fun c ↦ (s c).2 := by
      have h := congrArg (permuteBlockAddress cycle.symm) hk
      simpa using h
    refine ⟨i, j, k, ?_⟩
    funext c
    change ((address i c, permuteBlockAddress cycle (address j) c),
      permuteBlockAddress cycle.symm (address k) c) = s c
    rw [congrFun hi c, congrFun hjForward c, congrFun hkForward c]
  · rintro ⟨i, j, k, rfl⟩
    constructor
    · constructor
      · exact (mem_support_iff _).2 ⟨i, rfl⟩
      · change (permuteBlockAddress cycle).symm
          (permuteBlockAddress cycle (address j)) ∈ support h
        simpa using (mem_support_iff (address j)).2 ⟨j, rfl⟩
    · change (permuteBlockAddress cycle.symm).symm
        (permuteBlockAddress cycle.symm (address k)) ∈ support h
      simpa using (mem_support_iff (address k)).2 ⟨k, rfl⟩

/-- The constituent at `tripleAddress i j k` is canonically the external product of source
constituent `i`, the cyclic orientation of constituent `j`, and the inverse-cyclic orientation
of constituent `k`.

Proof sketch: identify each source constituent with its block-transported copy in
`partitioned T`.  Permute the second and third identifications, compose with the canonical block
casts used by `PartitionedTensor.permute`, and take the two external products. -/
theorem cyclicTriple_constituent_tripleAddress_isomorphic
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z))
    (i j k : Fin h) :
    Isomorphic
      (Tensor.external
        (Tensor.external (T i) (Tensor.permute cycle (T j)))
        (Tensor.permute cycle.symm (T k)))
      ((cyclicTriple T).constituent (tripleAddress i j k)) := by
  let P := partitioned T
  have hi : Isomorphic (T i) (P.constituent (address i)) :=
    partitioned_constituent_address_isomorphic T i
  have hjBase : Isomorphic (T j) (P.constituent (address j)) :=
    partitioned_constituent_address_isomorphic T j
  have hkBase : Isomorphic (T k) (P.constituent (address k)) :=
    partitioned_constituent_address_isomorphic T k
  let sj := permuteBlockAddress cycle (address j)
  let sk := permuteBlockAddress cycle.symm (address k)
  have hsj : (permuteBlockAddress cycle).symm sj = address j := by
    exact (permuteBlockAddress cycle).symm_apply_apply (address j)
  have hsk : (permuteBlockAddress cycle.symm).symm sk = address k := by
    exact (permuteBlockAddress cycle.symm).symm_apply_apply (address k)
  have hjBase' : Isomorphic (T j) (P.constituent ((permuteBlockAddress cycle).symm sj)) := by
    rw [hsj]
    exact hjBase
  have hkBase' : Isomorphic (T k)
      (P.constituent ((permuteBlockAddress cycle.symm).symm sk)) := by
    rw [hsk]
    exact hkBase
  have hjCast : Isomorphic
      (Tensor.permute cycle (P.constituent ((permuteBlockAddress cycle).symm sj)))
      ((P.permute cycle).constituent sj) := by
    exact Isomorphic.map
      (Tensor.permute cycle (P.constituent ((permuteBlockAddress cycle).symm sj)))
      (fun c ↦ permuteBlockSpaceCast
        (K := K) (V := BlockSpace X Y Z h) cycle sj c)
  have hkCast : Isomorphic
      (Tensor.permute cycle.symm
        (P.constituent ((permuteBlockAddress cycle.symm).symm sk)))
      ((P.permute cycle.symm).constituent sk) := by
    exact Isomorphic.map
      (Tensor.permute cycle.symm
        (P.constituent ((permuteBlockAddress cycle.symm).symm sk)))
      (fun c ↦ permuteBlockSpaceCast
        (K := K) (V := BlockSpace X Y Z h) cycle.symm sk c)
  have hj := (hjBase'.permute_legs cycle).trans hjCast
  have hk := (hkBase'.permute_legs cycle.symm).trans hkCast
  have hproduct := Isomorphic.external (Isomorphic.external hi hj) hk
  change Isomorphic
    (Tensor.external
      (Tensor.external (T i) (Tensor.permute cycle (T j)))
      (Tensor.permute cycle.symm (T k)))
    (Tensor.external
      (Tensor.external (P.constituent (address i))
        ((P.permute cycle).constituent sj))
      ((P.permute cycle.symm).constituent sk))
  exact hproduct

/-- Nonnegative leg weights implementing the C-tensor matrix-to-scalar degeneration.  Their sum
on `tripleAddress i j k` is `3*h^2 + (i+j-k)^2`. -/
def antidiagonalWeight (h : ℕ) : ∀ c, TripleBlockIndex h c → ℕ
  | .X, q => (q.1.1.val + h - q.2.val) ^ 2
  | .Y, q => q.1.2.val ^ 2 + 2 * q.1.1.val * q.1.2.val +
      2 * h * (h - q.1.1.val)
  | .Z, q => 2 * q.2.val * (h - q.1.2.val)

/-- The leading degree used by the antidiagonal weighting. -/
def antidiagonalDegree (h : ℕ) : ℕ := 3 * h ^ 2

/-- Integer form of the exact weight identity.  This form avoids any ambiguity about natural
subtraction when displaying the square `(i+j-k)^2`.

Proof sketch: `i,k<h` justify the two natural subtractions.  After casting them to integers, the
claim is the polynomial identity
`(i+h-k)^2 + j^2 + 2ij + 2h(h-i) + 2k(h-j) = 3h^2 + (i+j-k)^2`. -/
theorem intCast_totalWeight_tripleAddress {h : ℕ} (i j k : Fin h) :
    (blockAddressTotalWeight (antidiagonalWeight h) (tripleAddress i j k) : ℤ) =
      3 * (h : ℤ) ^ 2 + ((i : ℤ) + (j : ℤ) - (k : ℤ)) ^ 2 := by
  have hi : i.val ≤ h := Nat.le_of_lt i.isLt
  have hj : j.val ≤ h := Nat.le_of_lt j.isLt
  have hk : k.val ≤ i.val + h := by omega
  simp only [blockAddressTotalWeight, antidiagonalWeight, tripleAddress_X,
    tripleAddress_Y, tripleAddress_Z]
  push_cast [Nat.cast_sub hi, Nat.cast_sub hj, Nat.cast_sub hk]
  ring

/-- Every supported cyclic-triple address has weight at least `3*h^2`. -/
theorem antidiagonalDegree_le_totalWeight
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z))
    (s : BlockAddress (TripleBlockIndex h)) (hs : s ∈ (cyclicTriple T).support) :
    antidiagonalDegree h ≤ blockAddressTotalWeight (antidiagonalWeight h) s := by
  rcases (mem_cyclicTriple_support_iff T s).1 hs with ⟨i, j, k, rfl⟩
  apply Int.ofNat_le.mp
  rw [intCast_totalWeight_tripleAddress]
  simp only [antidiagonalDegree, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  nlinarith [sq_nonneg ((i : ℤ) + (j : ℤ) - (k : ℤ))]

/-- A supported cyclic-triple address has minimum weight exactly when its three indices lie on
the antidiagonal `i+j=k`. -/
theorem totalWeight_eq_antidiagonalDegree_iff {h : ℕ} (i j k : Fin h) :
    blockAddressTotalWeight (antidiagonalWeight h) (tripleAddress i j k) =
        antidiagonalDegree h ↔
      i.val + j.val = k.val := by
  have hweight := intCast_totalWeight_tripleAddress i j k
  constructor
  · intro hmin
    rw [hmin] at hweight
    simp only [antidiagonalDegree, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hweight
    have hsquare : (i : ℤ) + (j : ℤ) - (k : ℤ) = 0 := by nlinarith
    have hcast : (i : ℤ) + (j : ℤ) = (k : ℤ) := sub_eq_zero.mp hsquare
    exact_mod_cast hcast
  · intro hijk
    have hcast : (i : ℤ) + (j : ℤ) = (k : ℤ) := by exact_mod_cast hijk
    rw [hcast, sub_self, zero_pow (by decide), add_zero] at hweight
    apply Int.ofNat_inj.mp
    simpa only [antidiagonalDegree, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hweight

/-- The selected antidiagonal subpartition of the cyclic triple. -/
noncomputable def antidiagonal
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :=
  (cyclicTriple T).selectAddresses
    (fun s ↦ blockAddressTotalWeight (antidiagonalWeight h) s = antidiagonalDegree h)

/-- Selecting the antidiagonal changes only the support, not the constituent stored at an
address. -/
@[simp] theorem antidiagonal_constituent
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z))
    (s : BlockAddress (TripleBlockIndex h)) :
    (antidiagonal T).constituent s = (cyclicTriple T).constituent s :=
  rfl

/-- Degree-aware form of the cyclic C-tensor antidiagonal degeneration.  The leading degree is
the explicit common minimum `3*h^2`. -/
theorem cyclicTriple_degeneratesAt_antidiagonal
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    PolynomialDegeneratesAt (antidiagonalDegree h)
      (cyclicTriple T).realize (antidiagonal T).realize := by
  exact PolynomialDegeneratesAt.partitionedSelectAddresses
    (antidiagonalWeight h) (cyclicTriple T) (antidiagonalDegree h)
    (antidiagonalDegree_le_totalWeight T)

/-- The cyclic triple polynomially degenerates to its minimum-weight antidiagonal subpartition. -/
theorem cyclicTriple_degenerates_antidiagonal
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    PolynomialDegenerates (cyclicTriple T).realize (antidiagonal T).realize :=
  (cyclicTriple_degeneratesAt_antidiagonal T).toPolynomialDegenerates

/-- The antidiagonal addresses are injective on every tensor leg.

Proof sketch: equality on X recovers `i,k`, equality on Y recovers `i,j`, and equality on Z
recovers `j,k`.  On the antidiagonal any one of these pairs determines the remaining index. -/
theorem antidiagonal_isLegwiseInjective
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    IsLegwiseInjective (antidiagonal T).support := by
  intro leg s hs t ht heq
  have hs' : s ∈ (cyclicTriple T).support ∧
      blockAddressTotalWeight (antidiagonalWeight h) s = antidiagonalDegree h := by
    simpa [antidiagonal] using hs
  have ht' : t ∈ (cyclicTriple T).support ∧
      blockAddressTotalWeight (antidiagonalWeight h) t = antidiagonalDegree h := by
    simpa [antidiagonal] using ht
  rcases hs' with ⟨hsSupport, hsWeight⟩
  rcases ht' with ⟨htSupport, htWeight⟩
  rcases (mem_cyclicTriple_support_iff T s).1 hsSupport with ⟨i, j, k, rfl⟩
  rcases (mem_cyclicTriple_support_iff T t).1 htSupport with ⟨i', j', k', rfl⟩
  have hsAnti := (totalWeight_eq_antidiagonalDegree_iff i j k).1 hsWeight
  have htAnti := (totalWeight_eq_antidiagonalDegree_iff i' j' k').1 htWeight
  cases leg with
  | X =>
      have hi : i = i' := congrArg (fun q ↦ q.1.1) heq
      have hk : k = k' := congrArg (fun q ↦ q.2) heq
      subst i'
      subst k'
      have hj : j = j' := Fin.ext (by omega)
      subst j'
      rfl
  | Y =>
      have hi : i = i' := congrArg (fun q ↦ q.1.1) heq
      have hj : j = j' := congrArg (fun q ↦ q.1.2) heq
      subst i'
      subst j'
      have hk : k = k' := Fin.ext (by omega)
      subst k'
      rfl
  | Z =>
      have hj : j = j' := congrArg (fun q ↦ q.1.2) heq
      have hk : k = k' := congrArg (fun q ↦ q.2) heq
      subst j'
      subst k'
      have hi : i = i' := Fin.ext (by omega)
      subst i'
      rfl

/-- Degree-aware C-tensor extraction from the cyclic-triple realization to the indexed direct sum
of all minimum-weight constituent products. -/
theorem cyclicTriple_degeneratesAt_indexedDirectSum
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    PolynomialDegeneratesAt (antidiagonalDegree h) (cyclicTriple T).realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily
          (V := ProductBlockSpace K
            (ProductBlockSpace K (BlockSpace X Y Z h)
              (PermutedBlockSpace cycle (BlockSpace X Y Z h)))
            (PermutedBlockSpace cycle.symm (BlockSpace X Y Z h)))
          (antidiagonal T).support)
        (fun s : (antidiagonal T).support ↦ (antidiagonal T).constituent s.1)) :=
  by
    simpa using (cyclicTriple_degeneratesAt_antidiagonal T).trans
      (PolynomialDegeneratesAt.of_restricts
        (Restricts.partitionedLegwiseInjective_to_indexedDirectSum
          (antidiagonal T) (antidiagonal_isLegwiseInjective T)))

/-- Relation-level C-tensor extraction: the cyclic triple degenerates to an indexed direct sum
of all minimum-weight constituent products. -/
theorem cyclicTriple_degenerates_indexedDirectSum
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    PolynomialDegenerates (cyclicTriple T).realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily
          (V := ProductBlockSpace K
            (ProductBlockSpace K (BlockSpace X Y Z h)
              (PermutedBlockSpace cycle (BlockSpace X Y Z h)))
            (PermutedBlockSpace cycle.symm (BlockSpace X Y Z h)))
          (antidiagonal T).support)
        (fun s : (antidiagonal T).support ↦ (antidiagonal T).constituent s.1)) :=
  (cyclicTriple_degeneratesAt_indexedDirectSum T).toPolynomialDegenerates

/-- Degree-aware literature-facing finite C-tensor extraction.  Its leading degree remains the
explicit antidiagonal degree because the preliminary isomorphism is a degree-zero restriction. -/
theorem cyclicTensor_degeneratesAt_indexedDirectSum
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    PolynomialDegeneratesAt (antidiagonalDegree h) (cyclicTensor T)
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily
          (V := ProductBlockSpace K
            (ProductBlockSpace K (BlockSpace X Y Z h)
              (PermutedBlockSpace cycle (BlockSpace X Y Z h)))
            (PermutedBlockSpace cycle.symm (BlockSpace X Y Z h)))
          (antidiagonal T).support)
        (fun s : (antidiagonal T).support ↦ (antidiagonal T).constituent s.1)) :=
  by
    simpa using (PolynomialDegeneratesAt.of_restricts
      (cyclicTensor_isomorphic_cyclicTriple T).restricts).trans
        (cyclicTriple_degeneratesAt_indexedDirectSum T)

/-- Generic finite C-tensor-to-common-target degeneration.  If every selected antidiagonal
constituent restricts to the same tensor `S`, the cyclic C-tensor degenerates to one independent
copy of `S` for every antidiagonal address.

Proof sketch: first apply the canonical antidiagonal degeneration.  The selected support is
legwise injective, so it is already realized as an indexed direct sum; apply the supplied exact
restriction independently in each summand.  Exact restrictions have displayed degree zero, so
the leading degree remains `antidiagonalDegree h`. -/
theorem cyclicTensor_degeneratesAt_constantIndexedDirectSum
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {W : Leg → Type*} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z))
    (S : Tensor3 K W)
    (hS : ∀ s : (antidiagonal T).support,
      Restricts ((antidiagonal T).constituent s.1) S) :
    PolynomialDegeneratesAt (antidiagonalDegree h) (cyclicTensor T)
      (Tensor.indexedDirectSum (fun _ : (antidiagonal T).support ↦ S)) := by
  simpa using (cyclicTensor_degeneratesAt_indexedDirectSum T).trans
    (PolynomialDegeneratesAt.of_restricts
      (Restricts.indexedDirectSum hS))

/-- Literature-facing finite C-tensor extraction.  The ordinary product of the three cyclic
orientations polynomially degenerates to an indexed direct sum containing at least
`h²/2` constituent products in the division-free sense proved above. -/
theorem cyclicTensor_degenerates_indexedDirectSum
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    PolynomialDegenerates (cyclicTensor T)
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily
          (V := ProductBlockSpace K
            (ProductBlockSpace K (BlockSpace X Y Z h)
              (PermutedBlockSpace cycle (BlockSpace X Y Z h)))
            (PermutedBlockSpace cycle.symm (BlockSpace X Y Z h)))
          (antidiagonal T).support)
        (fun s : (antidiagonal T).support ↦ (antidiagonal T).constituent s.1)) :=
  (cyclicTensor_degeneratesAt_indexedDirectSum T).toPolynomialDegenerates

end CTensor

end AlgebraicComplexity
