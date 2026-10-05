/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrization
import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingValue
import AlgebraicComplexity.MatrixMultiplication.SymSixPowerWeight
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoConstituentValues
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeafTauWeight
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeafTauWeightBeta

/-!
# Six-orientation letter weights for the Duan--Wu--Zhou level-two endpoint

`Examples/DuanWuZhouLevelTwoConstituentValues.lean` supplies the fifteen per-constituent
`tau`-weights of `[DuanWuZhou2022]` section 6.3.  The asymmetric bypass does not consume them
directly: its letters are letters of `Tensor/PartitionedSymmetrization.lean`'s `symSixPartition`,
whose block labels are *six-tuples* of coarse addresses, one per leg permutation.  This module
converts between the two.

## The structural observation

`symSixPartition P` is, by construction, the six-fold partitioned external product in exactly the
association of `symSix_eq_sixOrientationProduct`.  Consequently the **diagonal** letter --- the
one whose six labels are the six leg-permutations of a single coarse address `s` --- has
constituent isomorphic to `sym_6` of `P.constituent s` on the nose
(`isomorphic_symSix_symSixPartition_diagonal`).  Every committed `sym_6` weight law therefore
applies to it verbatim, and no re-association or commutation of `Tensor.external` is needed
anywhere in this file.

## Principal results

* `isomorphic_symSix_symSixPartition_diagonal` --- `sym_6(P.constituent s)` is the diagonal
  letter's constituent.  The only content is that the six `PartitionedTensor.permute` block-space
  casts are isomorphisms (`Tensor.Isomorphic.map`).
* `hasTauWeight_symSixPartition_diagonal` --- a weight `v` on `P.constituent s` is a weight
  `v ^ 6` on the diagonal letter.  This is `HasTauWeight.symThree_pow_three` followed by
  `HasTauWeight.symSix_pow_two`, transported.
* `hasTauWeight_power_symSixPartition_diagonal` --- the same, read on the diagonal letter: a
  weight on a *block of `N` consecutive equal letters*, which is exactly the group-weight shape
  `hasTauWeight_restrictedSplittingPower_of_wordTensor`
  (`MatrixMultiplication/RestrictedSplittingValue.lean`) absorbs.
* `dwz63_hasTauWeight_symSix_ordinary` --- the twelve non-rotational components, unconditionally,
  at `dwz63ValOf s ^ 6`.
* `dwz63_hasTauWeight_power_symSix_112` --- the `T_{1,1,2}` orbit group weight
  `(dwz112LeafTerm ^ (3 * (D * k))) ^ 2`, **unconditionally**: the leaf lane's
  `exists_eventually_dwz112ConstituentHasTauWeight` is already committed, so no hypothesis is
  needed for `(1,1,2)`.
* `dwz63_hasTauWeight_power_symSix_121` --- the same at the free split `beta`, also
  unconditionally, from the leaf lane's `exists_eventually_dwz121ConstituentHasTauWeight`;
* `dwz63_hasTauWeight_power_symSix_orbit_of_leafShape` --- the shape-generic form.

## The join with the leaf lane

`dwz63LogVal112_eq_dwz112LogValue` and `dwz63LogVal121_eq_dwz121LogValue` identify this lane's two
orbit factors with the leaf lane's achieved values.  Both leaf modules are import-independent of
the values lane, so the identification is made here and only here.  Together with
`dwz63_logVal_eq` they close the loop: `dwz63LogVal` is the `alpha`-weighted sum of six factors,
of which the twelve non-rotational ones are discharged in
`Examples/DuanWuZhouLevelTwoConstituentValues.lean` and the `(1,1,2)`-orbit ones are the leaf
lane's `dwz112LogValue` and `dwz121LogValue`.

## Layering note

`symSixDiagonalAddress`, `isomorphic_symSix_symSixPartition_diagonal`,
`symSixDiagonalAddress`, `isomorphic_symSix_symSixPartition_diagonal` and
`hasTauWeight_symSixPartition_diagonal` mention no named tensor and belong in
`Tensor/PartitionedSymmetrization.lean`.  They are carried here only because that file belongs to
another lane; promoting them is a pure move.  The group step itself is *not* duplicated: it is the
tensor lane's committed `hasTauWeight_power_symSix_of_power_symThree`
(`MatrixMultiplication/SymSixPowerWeight.lean`).

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w

noncomputable section

/-! ## The diagonal letter of a six-orientation partition -/

section Generic

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The diagonal letter of `symSixPartition`**: the block label whose six components are the six
leg-permutations of a single coarse address `s`.  The association is that of
`PartitionedTensor.symSixPartition`, hence of `symSix_eq_sixOrientationProduct`. -/
def symSixDiagonalAddress (s : BlockAddress A) :=
  blockAddressProductEquiv
    (blockAddressProductEquiv
        (blockAddressProductEquiv (s, permuteBlockAddress cycle s),
          permuteBlockAddress cycle.symm s),
      blockAddressProductEquiv
        (blockAddressProductEquiv (permuteBlockAddress swapXY s,
            permuteBlockAddress (cycle.trans swapXY) s),
          permuteBlockAddress (cycle.symm.trans swapXY) s))

/-- A permuted partition's constituent at a permuted address is isomorphic to the leg permutation
of the source constituent: the block-space cast of `PartitionedTensor.permute` is a family of
linear equivalences. -/
theorem isomorphic_permute_partitionedPermute_constituent
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation)
    (s : BlockAddress (PermutedBlockIndex e A)) :
    Isomorphic (Tensor.permute e (P.constituent ((permuteBlockAddress e).symm s)))
      ((P.permute e).constituent s) :=
  Isomorphic.map _ (fun c ↦ permuteBlockSpaceCast (K := K) (V := V) e s c)

/-- The same, at a diagonal address. -/
theorem isomorphic_permute_partitionedPermute_constituent_apply
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation) (s : BlockAddress A) :
    Isomorphic (Tensor.permute e (P.constituent s))
      ((P.permute e).constituent (permuteBlockAddress e s)) := by
  have h := isomorphic_permute_partitionedPermute_constituent P e (permuteBlockAddress e s)
  rwa [Equiv.symm_apply_apply] at h

/-- **`sym₆` of a constituent is the diagonal letter of the six-orientation partition.**

`symSix_eq_sixOrientationProduct` puts `sym₆` into the six-factor association that
`symSixPartition` is built in; the six factors then differ only by the block-space casts, which
are isomorphisms. -/
theorem isomorphic_symSix_symSixPartition_diagonal
    (P : PartitionedTensor (K := K) (A := A) V) (s : BlockAddress A) :
    Isomorphic (symSix K (P.constituent s))
      (P.symSixPartition.constituent (symSixDiagonalAddress s)) := by
  rw [symSix_eq_sixOrientationProduct]
  refine Isomorphic.external ?_ ?_
  · exact ((Isomorphic.refl _).external
      (isomorphic_permute_partitionedPermute_constituent_apply P cycle s)).external
      (isomorphic_permute_partitionedPermute_constituent_apply P cycle.symm s)
  · exact ((isomorphic_permute_partitionedPermute_constituent_apply P swapXY s).external
      (isomorphic_permute_partitionedPermute_constituent_apply P (cycle.trans swapXY) s)).external
      (isomorphic_permute_partitionedPermute_constituent_apply P
        (cycle.symm.trans swapXY) s)

/-- **A weight `v` on a constituent is a weight `v ^ 6` on the diagonal six-orientation letter.**

The six leg-permuted copies each carry `v` (`HasTauWeight.permute`) and weights multiply; the
bookkeeping is done once and for all by `HasTauWeight.symThree_pow_three` followed by
`HasTauWeight.symSix_pow_two`. -/
theorem hasTauWeight_symSixPartition_diagonal
    (P : PartitionedTensor (K := K) (A := A) V) (s : BlockAddress A) {τ v : ℝ}
    (hv : 0 ≤ v) (h : HasTauWeight K (P.constituent s) τ v) :
    HasTauWeight K (P.symSixPartition.constituent (symSixDiagonalAddress s)) τ (v ^ 6) := by
  have h3 : HasTauWeight K (symThree K (P.constituent s)) τ (v ^ 3) :=
    h.symThree_pow_three hv
  have h6 : HasTauWeight K (symSix K (P.constituent s)) τ ((v ^ 3) ^ 2) :=
    h3.symSix_pow_two (by positivity)
  have hpow : (v ^ 3) ^ 2 = v ^ 6 := by ring
  rw [hpow] at h6
  exact h6.of_restricts (isomorphic_symSix_symSixPartition_diagonal P s).symm.restricts

end Generic

/-! ## The two shapes combined -/

section Group

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The group weight of a block of `n+1` equal diagonal six-orientation letters.**

The hypothesis is exactly the shape the `(112)` leaf chain produces: a weight on a power of
`sym₃` of the coarse constituent.  The conclusion is a weight on the external product over a
block of `n+1` consecutive positions all carrying the diagonal letter at `s`, which is what
`hasTauWeight_restrictedSplittingPower_of_wordTensor` consumes as one group of the word. -/
theorem hasTauWeight_power_symSixPartition_diagonal
    (P : PartitionedTensor (K := K) (A := A) V) (s : BlockAddress A) {τ w : ℝ} {M : ℕ}
    (hM : 0 < M) (hw : 0 ≤ w)
    (h : HasTauWeight K (Tensor.power (symThree K (P.constituent s)) M) τ w) :
    HasTauWeight K
      (Tensor.power (P.symSixPartition.constituent (symSixDiagonalAddress s)) M) τ (w ^ 2) :=
  (hasTauWeight_power_symSix_of_power_symThree hM h hw).of_restricts
    ((isomorphic_symSix_symSixPartition_diagonal P s).power M).symm.restricts

end Group

/-! ## The twelve non-rotational six-orientation letters -/

section Dwz

variable (K : Type u) [CommRing K]

/-- Every section 6.3 component value is nonnegative: each is an exponential. -/
theorem dwz63ValOf_nonneg (s : CWSquareAddress) : 0 ≤ dwz63ValOf s := by
  simp only [dwz63ValOf, dwz63Val004, dwz63Val013, dwz63Val022, dwz63Val112, dwz63Val121,
    dwz63Val220]
  split_ifs <;> exact (Real.exp_pos _).le

/-- **The twelve non-rotational components, as six-orientation letters.**

Each carries the sixth power of its section 6.3 value.  No hypothesis: the underlying weights are
the unconditional ones of `Examples/DuanWuZhouLevelTwoConstituentValues.lean`. -/
theorem dwz63_hasTauWeight_symSix_ordinary
    (s : CWSquareAddress)
    (h : HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent s)
      dwz63Tau (dwz63ValOf s)) :
    HasTauWeight K
      ((cwSquarePartitionedTensor K dwz63Q).symSixPartition.constituent
        (symSixDiagonalAddress s))
      dwz63Tau (dwz63ValOf s ^ 6) :=
  hasTauWeight_symSixPartition_diagonal _ s (dwz63ValOf_nonneg s) h

end Dwz

section DwzOrbit

variable (K : Type u) [Field K]

/-! ### The join with the leaf lane's achieved values -/

/-- **The `(1,1,2)` factor of `dwz63LogVal` is the leaf lane's `dwz112LogValue`.**

The `(1,1,2)` split is `b = 21015/10^8`; clearing the `1/3` gives the leaf lane's coefficients
`(1-2b)/3 = 9995797/(3*10^7)` and `2b/3 = 4203/(3*10^7)`, and `(2-2b) = 19995797/10^7`.  The
`log 6` of the leaf form expands to `log 2 + log 3`. -/
theorem dwz63LogVal112_eq_dwz112LogValue : dwz63LogVal112 = dwz112LogValue := by
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [dwz63LogVal112, dwz112LogValue, dwz63B, h6]
  ring

/-- **The `(1,2,1)` / `(2,1,1)` factor of `dwz63LogVal` is the leaf lane's `dwz121LogValue`.**

The leaf lane states its value in this lane's paper form as `dwz121LogValue_eq_paperForm`, so the
identification is a single rewrite. -/
theorem dwz63LogVal121_eq_dwz121LogValue : dwz63LogVal121 = dwz121LogValue := by
  rw [dwz121LogValue_eq_paperForm, dwz63LogVal121]

/-- **The `T_{1,1,2}` orbit group weight, unconditionally.**

`exists_eventually_dwz112ConstituentHasTauWeight` (the committed leaf-lane theorem) supplies a
weight on `sym₃` of the coarse `(1,1,2)` constituent raised to `D k`; squaring it gives the
six-orientation group weight over a block of `D k` consecutive diagonal `(1,1,2)` letters. -/
theorem dwz63_hasTauWeight_power_symSix_112 :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power
          ((cwSquarePartitionedTensor K dwz63Q).symSixPartition.constituent
            (symSixDiagonalAddress cwSquare112))
          (dwz112Mass * k))
        dwz63Tau ((dwz112LeafTerm K ^ (3 * (dwz112Mass * k))) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz112ConstituentHasTauWeight K
  refine ⟨max N 1, fun k hk ↦ ?_⟩
  have hk1 : 0 < k := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right N 1) hk)
  have hM : 0 < dwz112Mass * k :=
    Nat.mul_pos (by norm_num [dwz112Mass_eq]) hk1
  exact hasTauWeight_power_symSixPartition_diagonal _ cwSquare112 hM
    (pow_nonneg (dwz112LeafTerm_pos K).le _) (hN k (le_trans (le_max_left N 1) hk))

/-- **The `(1,2,1)` / `(2,1,1)` orbit group weight at the free split `beta`, unconditionally.**

The leaf lane's `beta` module certifies the same object --- a power of `sym_3` of the coarse
`(1,1,2)` constituent, since the three orbit addresses are the cyclic rotations of one another ---
at the mass `dwz121Mass` and the term `dwz121LeafTerm`.  Squaring gives the six-orientation group
weight over a block of `m+1` consecutive diagonal orbit letters. -/
theorem dwz63_hasTauWeight_power_symSix_121 :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power
          ((cwSquarePartitionedTensor K dwz63Q).symSixPartition.constituent
            (symSixDiagonalAddress cwSquare112))
          (dwz121Mass * k))
        dwz63Tau ((dwz121LeafTerm K ^ (3 * (dwz121Mass * k))) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz121ConstituentHasTauWeight K
  refine ⟨max N 1, fun k hk ↦ ?_⟩
  have hk1 : 0 < k := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right N 1) hk)
  have hM : 0 < dwz121Mass * k :=
    Nat.mul_pos (by norm_num [dwz121Mass_eq]) hk1
  exact hasTauWeight_power_symSixPartition_diagonal _ cwSquare112 hM
    (pow_nonneg (dwz121LeafTerm_pos K).le _) (hN k (le_trans (le_max_left N 1) hk))

/-- **The same, for a general orbit address and leaf term.**

This is the form the `beta`-orbit module for `(1,2,1)` and `(2,1,1)` instantiates: whatever
address `s` and term `t` its join theorem produces, the six-orientation group weight over a block
of `m+1` positions is `(t ^ (3 * (m+1))) ^ 2`. -/
theorem dwz63_hasTauWeight_power_symSix_orbit_of_leafShape
    (s : CWSquareAddress) (t : ℝ) (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M)
    (h : HasTauWeight K
      (Tensor.power (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent s)) M)
      dwz63Tau (t ^ (3 * M))) :
    HasTauWeight K
      (Tensor.power
        ((cwSquarePartitionedTensor K dwz63Q).symSixPartition.constituent
          (symSixDiagonalAddress s))
        M)
      dwz63Tau ((t ^ (3 * M)) ^ 2) :=
  hasTauWeight_power_symSixPartition_diagonal _ s hM (pow_nonneg ht _) h

end DwzOrbit

end

end AlgebraicComplexity.Examples
