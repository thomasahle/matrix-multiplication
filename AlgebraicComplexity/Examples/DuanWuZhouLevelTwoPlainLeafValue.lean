/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SymSixDistribution
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSixOrientationValues
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSupportBridge
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitAssembly
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAlphaAddressCells

set_option autoImplicit false

/-!
# The value of the plain-partition uniform leaf

Layer 4 (`AlgebraicComplexity/Examples/`).  The value side of the plain fifteen-block route: it
peels the three exceptional-orbit blocks off a `sym_6` word, weighs the remaining bulk letterwise,
and assembles the two into the leaf weight the stage consumes.  Its endpoint is
`dwz63_hasTauWeight_symSix_plainLeaf_logVal`, which delivers a `HasTauWeight` for the plain uniform
leaf at `exp dwz63LogVal`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173 (`[DuanWuZhou2022]`), `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

/-! ## `sym₆` of a word tensor, letterwise

`PROMOTE:` nothing here mentions a named tensor; this belongs next to
`hasTauWeight_wordTensor` in `MatrixMultiplication/RestrictedSplittingValue.lean`, or in
`Tensor/SymSixDistribution.lean`.  It is kept here only to avoid re-posting an arbitrated hash.
-/

section Generic

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The six-symmetrization of a word tensor carries the product of the letterwise
six-symmetrized weights.**

The exact analogue of `hasTauWeight_wordTensor` with `sym₆` applied throughout: `sym₆` distributes
over the external product (`Tensor.Isomorphic.symSix_external`), so the induction is the same one,
one factor at a time.  This is the form `[DuanWuZhou2022]` section 6 needs, because there `sym₆` is
applied *once*, to the whole leaf, and has to be pushed down onto the per-component values. -/
theorem hasTauWeight_symSix_wordTensor
    (P : PartitionedTensor (K := K) (A := A) V) {τ : ℝ} {value : P.support → ℝ}
    (hvalue : ∀ s, 0 ≤ value s)
    (h : ∀ s : P.support, HasTauWeight K (symSix K (P.constituent s.1)) τ (value s)) :
    ∀ (n : ℕ) (q : PositiveWord P.support n),
      HasTauWeight K (symSix K (PartitionedTensor.positiveSupportWordTensor P n q)) τ
        (positiveSupportWordWeight value n q)
  | 0, q => h q
  | n + 1, q => by
      rw [PartitionedTensor.positiveSupportWordTensor_succ]
      refine HasTauWeight.of_restricts
        (Tensor.Isomorphic.symSix_external _ _).restricts ?_
      exact HasTauWeight.external
        (hasTauWeight_symSix_wordTensor P hvalue h n q.1) (h q.2)
        (positiveSupportWordWeight_nonneg hvalue n q.1) (hvalue q.2)

/-! ## Peeling three letters, with the residual multiplicities recorded

`Isomorphic.positiveSupportWordTensor_peel3` of
`Examples/DuanWuZhouLevelTwoOrbitAssembly.lean` returns the residual multiplicities only away from
the three peeled letters.  A bulk *value* computation also needs them to be zero *at* those
letters, so that a letter valued `0` contributes `0 ^ 0 = 1` rather than `0`.  This variant keeps
the full pointwise relation, from which both facts follow by `omega`.

`MERGE:` this should replace `…_peel3` there; it is strictly stronger and the proof is the same
three applications of `…_peel`. -/
namespace Tensor

theorem Isomorphic.positiveSupportWordTensor_peel3_full
    (P : PartitionedTensor (K := K) (A := A) V) {n m ka kb kc : ℕ}
    (q : PositiveWord P.support n) (sa sb sc : P.support)
    (hab : sa ≠ sb) (hac : sa ≠ sc) (hbc : sb ≠ sc)
    (hn : n = m + ka + kb + kc + 3)
    (hma : WordType.multiplicity (positiveWordEquiv P.support n q) sa = ka + 1)
    (hmb : WordType.multiplicity (positiveWordEquiv P.support n q) sb = kb + 1)
    (hmc : WordType.multiplicity (positiveWordEquiv P.support n q) sc = kc + 1) :
    ∃ u : PositiveWord P.support m,
      (∀ j : P.support, WordType.multiplicity (positiveWordEquiv P.support n q) j =
        WordType.multiplicity (positiveWordEquiv P.support m u) j
          + (if j = sa then ka + 1 else 0) + (if j = sb then kb + 1 else 0)
          + (if j = sc then kc + 1 else 0)) ∧
      Isomorphic (PartitionedTensor.positiveSupportWordTensor P n q)
        (Tensor.external
          (Tensor.external
            (Tensor.external (PartitionedTensor.positiveSupportWordTensor P m u)
              (Tensor.power (P.constituent sa.1) (ka + 1)))
            (Tensor.power (P.constituent sb.1) (kb + 1)))
          (Tensor.power (P.constituent sc.1) (kc + 1))) := by
  obtain ⟨u₁, h₁m, h₁i⟩ := Tensor.Isomorphic.positiveSupportWordTensor_peel P
    (m := m + ka + kb + 2) (k := kc) (by omega) q sc hmc
  have hmb₁ : WordType.multiplicity
      (positiveWordEquiv P.support (m + ka + kb + 2) u₁) sb = kb + 1 := by
    have h := h₁m sb
    rw [if_neg hbc] at h
    omega
  obtain ⟨u₂, h₂m, h₂i⟩ := Tensor.Isomorphic.positiveSupportWordTensor_peel P
    (m := m + ka + 1) (k := kb) (by omega) u₁ sb hmb₁
  have hma₂ : WordType.multiplicity
      (positiveWordEquiv P.support (m + ka + 1) u₂) sa = ka + 1 := by
    have h1 := h₁m sa
    have h2 := h₂m sa
    rw [if_neg hac] at h1
    rw [if_neg hab] at h2
    omega
  obtain ⟨u₃, h₃m, h₃i⟩ := Tensor.Isomorphic.positiveSupportWordTensor_peel P
    (m := m) (k := ka) (by omega) u₂ sa hma₂
  refine ⟨u₃, fun j ↦ ?_, ?_⟩
  · have h1 := h₁m j
    have h2 := h₂m j
    have h3 := h₃m j
    by_cases hja : j = sa <;> by_cases hjb : j = sb <;> by_cases hjc : j = sc <;>
      simp only [hja, hjb, hjc, if_true, if_false] at h1 h2 h3 ⊢ <;> omega
  · exact h₁i.trans ((h₂i.trans (h₃i.external (Isomorphic.refl _))).external
      (Isomorphic.refl _))

/-! ## `sym₆` of a peeled word tensor -/

/-- **The four blocks a triple peel leaves, six-symmetrized.**

`sym₆` distributes over the external product and over a positive power, so the four blocks a
triple peel produces --- a bulk word tensor and three constant powers --- each get symmetrized in
place.  This is the diagonal locking made concrete: the six orientations of a block stay with that
block. -/
theorem Isomorphic.symSix_peel3_blocks
    (P : PartitionedTensor (K := K) (A := A) V) {m ka kb kc : ℕ}
    (u : PositiveWord P.support m) (sa sb sc : P.support) :
    Isomorphic
      (symSix K
        (Tensor.external
          (Tensor.external
            (Tensor.external (PartitionedTensor.positiveSupportWordTensor P m u)
              (Tensor.power (P.constituent sa.1) (ka + 1)))
            (Tensor.power (P.constituent sb.1) (kb + 1)))
          (Tensor.power (P.constituent sc.1) (kc + 1))))
      (Tensor.external
        (Tensor.external
          (Tensor.external
            (symSix K (PartitionedTensor.positiveSupportWordTensor P m u))
            (Tensor.power (symSix K (P.constituent sa.1)) (ka + 1)))
          (Tensor.power (symSix K (P.constituent sb.1)) (kb + 1)))
        (Tensor.power (symSix K (P.constituent sc.1)) (kc + 1))) := by
  refine (Tensor.Isomorphic.symSix_external _ _).trans ?_
  refine Isomorphic.external ?_ (Tensor.Isomorphic.symSix_power_positive _ kc)
  refine (Tensor.Isomorphic.symSix_external _ _).trans ?_
  refine Isomorphic.external ?_ (Tensor.Isomorphic.symSix_power_positive _ kb)
  refine (Tensor.Isomorphic.symSix_external _ _).trans ?_
  exact Isomorphic.external (Isomorphic.refl _)
    (Tensor.Isomorphic.symSix_power_positive _ ka)

end Tensor

end Generic

namespace Examples

open AlgebraicComplexity Tensor

/-! ## The orbit cells, six-symmetrized

Under the diagonal reading there are no tags: the three `(1,1,2)`-orbit cells are separate letters
of the *coarse* partition, and each contributes its own block `sym₆(T_s)^{⊗ m_s}`.  All three are
covered by the `beta`-split certificate at the orbit-maximal value `V_(1,2,1)`, because the three
coarse constituents are leg rotations of one another and `sym₃` is rotation-invariant. -/

section Orbit

variable (K : Type u) [Field K]

/-- The three orbit constituents have isomorphic three-symmetrizations: they are leg rotations of
one another and `sym₃` is rotation-invariant. -/
theorem dwz63_isomorphic_symThree_orbitCell (s : CWSquareAddress) (hs : s ∈ cwSquare112Orbit) :
    Isomorphic (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent s))
      (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)) := by
  simp only [cwSquare112Orbit, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · exact Isomorphic.refl _
  · exact (AlgebraicComplexity.Isomorphic.symThree_congr
      (cwSquareConstituent_121_isomorphic_cycleSymm K dwz63Q)).trans
      (AlgebraicComplexity.Isomorphic.symThree_permute_cycleSymm _)
  · exact (AlgebraicComplexity.Isomorphic.symThree_congr
      (cwSquareConstituent_211_isomorphic_cycle K dwz63Q)).trans
      (AlgebraicComplexity.Isomorphic.symThree_permute_cycle _)

/-- **The orbit block weight at any of the three orbit cells.**

`exists_eventually_dwz121ConstituentHasTauWeight` is stated at `(1,1,2)`; rotation invariance of
`sym₃` carries it to `(1,2,1)` and `(2,1,1)`, and squaring lifts it from `sym₃` to `sym₆`.  This is
the orbit-maximal choice: all three cells are valued at `V_(1,2,1)`, which is what makes the
`alpha`-weighted comparison go through even though `alpha` is not constant on the orbit. -/
theorem dwz63_hasTauWeight_power_symSix_orbitCell
    (s : CWSquareAddress) (hs : s ∈ cwSquare112Orbit) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent s))
          (dwz121Mass * k))
        dwz63Tau ((dwz121LeafTerm K ^ (3 * (dwz121Mass * k))) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz121ConstituentHasTauWeight K
  refine ⟨max N 1, fun k hk ↦ ?_⟩
  have hk1 : 0 < k := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right N 1) hk)
  have hM : 0 < dwz121Mass * k := Nat.mul_pos (by norm_num [dwz121Mass_eq]) hk1
  have hbase := hN k (le_trans (le_max_left N 1) hk)
  have hs3 : HasTauWeight K
      (Tensor.power (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent s))
        (dwz121Mass * k)) dwz63Tau (dwz121LeafTerm K ^ (3 * (dwz121Mass * k))) :=
    hbase.of_restricts
      ((dwz63_isomorphic_symThree_orbitCell K s hs).power (dwz121Mass * k)).restricts
  have hdiag := dwz63_hasTauWeight_power_symSix_orbit_of_leafShape K s (dwz121LeafTerm K)
    (dwz121LeafTerm_pos K).le hM hs3
  exact hdiag.of_restricts
    ((isomorphic_symSix_symSixPartition_diagonal (cwSquarePartitionedTensor K dwz63Q)
      s).power (dwz121Mass * k)).restricts

end Orbit

/-! ## The plain-partition uniform leaf, six-symmetrized -/

section PlainLeaf

variable (K : Type u) [Field K]

/-- **The six-symmetrized coarse cell value.**  The sixth power of the section 6.3 cell value off
the `(1,1,2)` orbit, and `0` on it --- no non-rotational value exists there.  The orbit letters are
peeled off before this function is used, so the `0` is only ever raised to the exponent `0`. -/
noncomputable def dwz63SymSixCellValue :
    (cwSquarePartitionedTensor K dwz63Q).support → ℝ :=
  fun s ↦ if s.1 ∈ cwSquare112Orbit then 0 else dwz63ValOf s.1 ^ 6

theorem dwz63SymSixCellValue_nonneg (s : (cwSquarePartitionedTensor K dwz63Q).support) :
    0 ≤ dwz63SymSixCellValue K s := by
  unfold dwz63SymSixCellValue
  split_ifs
  · exact le_rfl
  · exact pow_nonneg (dwz63ValOf_nonneg _) 6

/-- **Every coarse letter carries its six-symmetrized value.**

Off the `(1,1,2)` orbit this is the committed cell weight cubed and squared
(`HasTauWeight.symThree_pow_three`, `HasTauWeight.symSix_pow_two`); on the orbit it is the trivial
weight `0`, which is all a peeled-off letter needs. -/
theorem dwz63_hasTauWeight_symSix_cell
    (hcell : ∀ s : (cwSquarePartitionedTensor K dwz63Q).support, s.1 ∉ cwSquare112Orbit →
      HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent s.1) dwz63Tau
        (dwz63ValOf s.1))
    (s : (cwSquarePartitionedTensor K dwz63Q).support) :
    HasTauWeight K (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent s.1)) dwz63Tau
      (dwz63SymSixCellValue K s) := by
  unfold dwz63SymSixCellValue
  split_ifs with hs
  · exact HasTauWeight.zero _ _
  · have h3 := (hcell s hs).symThree_pow_three (dwz63ValOf_nonneg _)
    have h6 := h3.symSix_pow_two (pow_nonneg (dwz63ValOf_nonneg _) 3)
    rwa [show ((dwz63ValOf s.1 ^ 3) ^ 2) = dwz63ValOf s.1 ^ 6 from by ring] at h6

set_option maxHeartbeats 1000000 in
/-- **The weight of the six-symmetrized plain-partition leaf.**

`[DuanWuZhou2022]` section 6 hashes the *plain* power and degenerates it onto a uniform leaf
`𝒯* = ⊗_s T_s^{⊗ n alpha_s}`; `sym₆` is applied once, at the end.  This theorem is that last step
for one such leaf, presented as a word over the fifteen coarse cells: peel the three
`(1,1,2)`-orbit letters into constant blocks, push `sym₆` onto the four blocks
(`Isomorphic.symSix_peel3_blocks`), weigh the bulk letterwise
(`hasTauWeight_symSix_wordTensor`) and the three orbit blocks by their certificates.

**No tags, no cyclic regrouping, no stranded letters.**  Each orbit cell is a separate coarse
letter contributing its own block `sym₆(T_s)^{⊗ m_s}`, and
`dwz63_hasTauWeight_power_symSix_orbitCell` covers all three at the orbit-maximal value.  The
per-tag imbalance of the six-orientation encoding
(`Examples/DuanWuZhouLevelTwoOrbitAssemblyValue.lean`) does not arise, because there are no
orientations to balance. -/
theorem dwz63_hasTauWeight_symSix_plainLeaf {n mb ka kb kc : ℕ}
    (q : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hcell : ∀ s : (cwSquarePartitionedTensor K dwz63Q).support, s.1 ∉ cwSquare112Orbit →
      HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent s.1) dwz63Tau
        (dwz63ValOf s.1))
    (sa sb sc : (cwSquarePartitionedTensor K dwz63Q).support)
    (hab : sa ≠ sb) (hac : sa ≠ sc) (hbc : sb ≠ sc)
    (hn : n = mb + ka + kb + kc + 3)
    (hma : WordType.multiplicity (positiveWordEquiv _ n q) sa = ka + 1)
    (hmb : WordType.multiplicity (positiveWordEquiv _ n q) sb = kb + 1)
    (hmc : WordType.multiplicity (positiveWordEquiv _ n q) sc = kc + 1)
    {wa wb wc : ℝ} (hwa0 : 0 ≤ wa) (hwb0 : 0 ≤ wb) (hwc0 : 0 ≤ wc)
    (hwa : HasTauWeight K
      (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent sa.1)) (ka + 1))
      dwz63Tau wa)
    (hwb : HasTauWeight K
      (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent sb.1)) (kb + 1))
      dwz63Tau wb)
    (hwc : HasTauWeight K
      (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent sc.1)) (kc + 1))
      dwz63Tau wc) :
    ∃ u : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) mb,
      (∀ j : (cwSquarePartitionedTensor K dwz63Q).support,
        WordType.multiplicity (positiveWordEquiv _ n q) j =
          WordType.multiplicity (positiveWordEquiv _ mb u) j
            + (if j = sa then ka + 1 else 0) + (if j = sb then kb + 1 else 0)
            + (if j = sc then kc + 1 else 0)) ∧
      HasTauWeight K
        (symSix K (PartitionedTensor.positiveSupportWordTensor
          (cwSquarePartitionedTensor K dwz63Q) n q)) dwz63Tau
        (positiveSupportWordWeight (dwz63SymSixCellValue K) mb u * wa * wb * wc) := by
  obtain ⟨u, hmult, hiso⟩ :=
    Isomorphic.positiveSupportWordTensor_peel3_full (cwSquarePartitionedTensor K dwz63Q)
      q sa sb sc hab hac hbc hn hma hmb hmc
  refine ⟨u, hmult, ?_⟩
  have hbulk := hasTauWeight_symSix_wordTensor (cwSquarePartitionedTensor K dwz63Q)
    (dwz63SymSixCellValue_nonneg K) (dwz63_hasTauWeight_symSix_cell K hcell) mb u
  have hbulk0 : 0 ≤ positiveSupportWordWeight (dwz63SymSixCellValue K) mb u :=
    positiveSupportWordWeight_nonneg (dwz63SymSixCellValue_nonneg K) mb u
  refine HasTauWeight.of_restricts
    (((Tensor.Isomorphic.symSix_congr hiso).trans
      (Isomorphic.symSix_peel3_blocks (cwSquarePartitionedTensor K dwz63Q)
        (ka := ka) (kb := kb) (kc := kc) u sa sb sc))).restricts ?_
  exact HasTauWeight.external
    (HasTauWeight.external (HasTauWeight.external hbulk hwa hbulk0 hwa0) hwb
      (mul_nonneg hbulk0 hwa0) hwb0) hwc
    (mul_nonneg (mul_nonneg hbulk0 hwa0) hwb0) hwc0

/-! ## The uniform direct sum: `m` copies of the leaf become `m⁶` copies of its symmetrization -/

/-- **The endpoint's weight from a uniform retention.**

`HasTauWeight.symSix_indexedDirectSum_uniform` (`Tensor/SymSixDistribution.lean`) applied to the
plain leaf: a construction retaining `Fintype.card ι` copies of *one* leaf carries
`(card ι)^6` times the leaf's symmetrized weight.  This is the step that meets a copy budget
stated per oriented letter from a hash that only produces copies per position. -/
theorem dwz63_hasTauWeight_symSix_uniformLeafSum {ι : Type w} [Fintype ι] [DecidableEq ι]
    {n mb ka kb kc : ℕ}
    (q : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hcell : ∀ s : (cwSquarePartitionedTensor K dwz63Q).support, s.1 ∉ cwSquare112Orbit →
      HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent s.1) dwz63Tau
        (dwz63ValOf s.1))
    (sa sb sc : (cwSquarePartitionedTensor K dwz63Q).support)
    (hab : sa ≠ sb) (hac : sa ≠ sc) (hbc : sb ≠ sc)
    (hn : n = mb + ka + kb + kc + 3)
    (hma : WordType.multiplicity (positiveWordEquiv _ n q) sa = ka + 1)
    (hmb : WordType.multiplicity (positiveWordEquiv _ n q) sb = kb + 1)
    (hmc : WordType.multiplicity (positiveWordEquiv _ n q) sc = kc + 1)
    {wa wb wc : ℝ} (hwa0 : 0 ≤ wa) (hwb0 : 0 ≤ wb) (hwc0 : 0 ≤ wc)
    (hwa : HasTauWeight K
      (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent sa.1)) (ka + 1))
      dwz63Tau wa)
    (hwb : HasTauWeight K
      (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent sb.1)) (kb + 1))
      dwz63Tau wb)
    (hwc : HasTauWeight K
      (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent sc.1)) (kc + 1))
      dwz63Tau wc) :
    ∃ u : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) mb,
      HasTauWeight K
        (symSix K (Tensor.indexedDirectSum
          (fun _ : ι ↦ PartitionedTensor.positiveSupportWordTensor
            (cwSquarePartitionedTensor K dwz63Q) n q))) dwz63Tau
        ((Fintype.card ι : ℝ) ^ 6 *
          (positiveSupportWordWeight (dwz63SymSixCellValue K) mb u * wa * wb * wc)) := by
  obtain ⟨u, _, hleaf⟩ := dwz63_hasTauWeight_symSix_plainLeaf K q hcell sa sb sc hab hac hbc hn
    hma hmb hmc hwa0 hwb0 hwc0 hwa hwb hwc
  exact ⟨u, HasTauWeight.symSix_indexedDirectSum_uniform hleaf⟩


end PlainLeaf


/-! ## The fifteen cells, evaluated -/

section Cells

/-- The three tables of the fifteen cells agree. -/
theorem dwz63CellAddress_eq_dwz63Cell (c : Fin 15) : dwz63CellAddress c = dwz63Cell c := by
  funext leg; cases leg <;> rfl

theorem dwz63Cell_eq_dwz63Component (c : Fin 15) : dwz63Cell c = dwz63Component c := by
  fin_cases c <;> rfl

/-- The profile at the `c`-th cell is that cell's `dwz63Alpha` entry. -/
theorem dwz63AlphaAddress_dwz63Cell (c : Fin 15) :
    dwz63AlphaAddress (dwz63Cell c) = dwz63Alpha c := by
  rw [← dwz63CellAddress_eq_dwz63Cell]
  refine dwz63AlphaAddress_cellAddress c fun j hj ↦ ?_
  rw [dwz63CellAddress_eq_dwz63Cell, dwz63CellAddress_eq_dwz63Cell]
  exact fun h ↦ hj (dwz63Cell_injective h)

/-- The value at the `c`-th cell is that cell's `dwz63Val` entry. -/
theorem dwz63ValOf_dwz63Cell (c : Fin 15) : dwz63ValOf (dwz63Cell c) = dwz63Val c := by
  rw [dwz63Cell_eq_dwz63Component, dwz63ValOf_dwz63Component]

/-- Exactly the three indices `6`, `7`, `10` name the `(1,1,2)` orbit. -/
theorem dwz63Cell_mem_orbit_iff (c : Fin 15) :
    dwz63Cell c ∈ cwSquare112Orbit ↔ (c = 6 ∨ c = 7 ∨ c = 10) := by
  revert c; decide

end Cells

/-! ## The bulk product, evaluated -/

section Bulk

variable (K : Type u) [Field K]

/-- The per-cell factor of the assembled bulk weight: the sixth power of the cell value at its
typical multiplicity off the `(1,1,2)` orbit, and `1` on it. -/
noncomputable def dwz63BulkFactor (t : ℕ) (c : Fin 15) : ℝ :=
  if c = 6 ∨ c = 7 ∨ c = 10 then 1 else dwz63Val c ^ (6 * (dwz63Alpha c * t))

end Bulk


/-! ## The orbit value comparison

The one numeric fact the orbit-maximal choice rests on: the `(1,2,1)` component is worth strictly
more than the `(1,1,2)` component, by enough to swallow the certificate's `10 ^ (-29)` reserve
many times over. -/

section Numeric

open AlgebraicComplexity.Analysis

/-- **An upper enclosure for `log 3`**, in the shape of the committed atom table.  The table has
only a *lower* enclosure for `3` (`dwz63_atom_v1_ge`); the orbit comparison needs the other
direction, because `log 2 + log 3` occurs on both sides of it with different coefficients. -/
theorem dwz63_atom_three_le : Real.log 3 ≤ (1098613 / 1000000 : ℝ) := by
  apply log_le_of_powTwo_add_logRatioUpper 1 10 log_two_le_sharp
      (logTwoUpper := (6931471806 / 10000000000 : ℝ)) (x := (1 / 5 : ℝ)) <;>
    norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- **The `(1,1,2)` component is worth strictly less than the `(1,2,1)` component.**

`dwz63LogVal112 + 10^(-3) ≤ dwz63LogVal121`.  Both are the same `lem:non-rot-values` (d) formula,
at the constrained split `b = 21015/10^8` and at the free split
`beta = 69022217/5·10^9` respectively; the free split wins.  The margin `10^(-3)` is far more than
the `(alpha(1,1,2) + 2 alpha(1,2,1)) / alpha(1,1,2) ≈ 3.06` multiple of the certificate reserve
`10^(-29)` that the value comparison has to absorb.

This is what licenses valuing all three `(1,1,2)`-orbit cells at `V_(1,2,1)`: the orbit-maximal
choice, which is forced because `alpha` is not constant on the orbit. -/
theorem dwz63_logVal112_add_le_logVal121 :
    dwz63LogVal112 + 1 / 1000 ≤ dwz63LogVal121 := by
  have h2u : Real.log 2 < 6931471808 / 10000000000 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have h2l := dwz63_atom_v0_ge
  have h3u := dwz63_atom_three_le
  have h3l := dwz63_atom_v1_ge
  have hp2 := dwz63_atom_p2_le
  have hp3 := dwz63_atom_p3_le
  have hv7 := dwz63_atom_v7_ge
  have hv8 := dwz63_atom_v8_ge
  unfold dwz63LogVal112 dwz63LogVal121 dwz63B dwz63Beta dwz63Tau
  nlinarith [h2u, h2l, h3u, h3l, hp2, hp3, hv7, hv8]

end Numeric

/-! ## The bulk weight, evaluated cellwise -/

section Closing

variable (K : Type u) [Field K]

set_option maxHeartbeats 1000000 in
/-- **The assembled bulk weight is the cellwise product.**

`positiveSupportWordWeight_eq_prod_pow` regroups the bulk word's weight by letter multiplicity;
`dwz63CellEquiv` transports that product from the coarse support to the fifteen-cell index.  The
three peeled orbit letters contribute `0 ^ 0 = 1`, which is exactly why the value function is
allowed to be `0` there. -/
theorem dwz63_bulkWeight_eq {t mb : ℕ}
    (u : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) mb)
    (hmu : ∀ s : (cwSquarePartitionedTensor K dwz63Q).support,
      WordType.multiplicity (positiveWordEquiv _ mb u) s =
        if s.1 ∈ cwSquare112Orbit then 0 else dwz63AlphaAddress s.1 * t) :
    positiveSupportWordWeight (dwz63SymSixCellValue K) mb u
      = ∏ c : Fin 15, dwz63BulkFactor t c := by
  classical
  let e : Fin 15 ≃ ((cwSquarePartitionedTensor K dwz63Q).support) := dwz63CellEquiv
  rw [positiveSupportWordWeight_eq_prod_pow]
  refine (Fintype.prod_equiv e (fun c ↦ dwz63BulkFactor t c)
    (fun s ↦ dwz63SymSixCellValue K s ^
      WordType.multiplicity (positiveWordEquiv _ mb u) s) ?_).symm
  intro c
  rw [hmu (e c)]
  show dwz63BulkFactor t c
      = (if dwz63Cell c ∈ cwSquare112Orbit then (0 : ℝ)
          else dwz63ValOf (dwz63Cell c) ^ 6) ^
        (if dwz63Cell c ∈ cwSquare112Orbit then 0 else dwz63AlphaAddress (dwz63Cell c) * t)
  rw [dwz63BulkFactor]
  by_cases hc : c = 6 ∨ c = 7 ∨ c = 10
  · have hmem : dwz63Cell c ∈ cwSquare112Orbit := (dwz63Cell_mem_orbit_iff c).mpr hc
    rw [if_pos hc, if_pos hmem, if_pos hmem, pow_zero]
  · have hmem : dwz63Cell c ∉ cwSquare112Orbit := fun h ↦ hc ((dwz63Cell_mem_orbit_iff c).mp h)
    rw [if_neg hc, if_neg hmem, if_neg hmem, dwz63ValOf_dwz63Cell,
      dwz63AlphaAddress_dwz63Cell, ← pow_mul]

/-- The three orbit indices, as a `Finset`. -/
theorem dwz63_filter_orbitIndices :
    (Finset.univ.filter fun c : Fin 15 ↦ c = 6 ∨ c = 7 ∨ c = 10) = {6, 7, 10} := by
  decide

set_option maxHeartbeats 1000000 in
/-- **The orbit factor of the target is dominated by the certificate's.**

The whole orbit-maximal argument in three factors: the target asks for
`V_(1,1,2)^(6 A t) · V_(1,2,1)^(12 B t)` and the certificate delivers
`dwz121LeafTerm^(6 (A + 2B) t)`.  `dwz63_logVal112_add_le_logVal121` supplies the `10^(-3)` of
slack at the `(1,1,2)` cell, which pays for the `10^(-29)` reserve at all three, with twenty-six
orders to spare. -/
theorem dwz63_orbitFactor_le (t : ℕ) :
    dwz63Val 6 ^ (6 * (dwz63Alpha 6 * t)) * dwz63Val 7 ^ (6 * (dwz63Alpha 7 * t))
        * dwz63Val 10 ^ (6 * (dwz63Alpha 10 * t))
      ≤ (dwz121LeafTerm K ^ (3 * (dwz63Alpha112 * t))) ^ 2 *
          (dwz121LeafTerm K ^ (3 * (dwz63Alpha121 * t))) ^ 2 *
          (dwz121LeafTerm K ^ (3 * (dwz63Alpha121 * t))) ^ 2 := by
  have hLT : (0 : ℝ) < dwz121LeafTerm K := dwz121LeafTerm_pos K
  have hlog : dwz63LogVal121 - 1 / 10 ^ 29 ≤ Real.log (dwz121LeafTerm K) := by
    rw [dwz63LogVal121_eq_dwz121LogValue]
    exact dwz121LogValue_sub_le_log_dwz121LeafTerm K
  have hgap := dwz63_logVal112_add_le_logVal121
  have h6 : dwz63Val 6 = Real.exp dwz63LogVal112 := rfl
  have h7 : dwz63Val 7 = Real.exp dwz63LogVal121 := rfl
  have h10 : dwz63Val 10 = Real.exp dwz63LogVal121 := rfl
  have hLTe : dwz121LeafTerm K = Real.exp (Real.log (dwz121LeafTerm K)) :=
    (Real.exp_log hLT).symm
  rw [h6, h7, h10, dwz63Alpha_six, dwz63Alpha_seven, dwz63Alpha_ten]
  rw [hLTe]
  simp only [← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hA : (dwz63Alpha112 : ℝ) = 20088623 := by norm_num [dwz63Alpha112]
  have hB : (dwz63Alpha121 : ℝ) = 20734458 := by norm_num [dwz63Alpha121]
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  push_cast
  rw [hA, hB]
  nlinarith [hlog, hgap, ht]

set_option maxHeartbeats 1000000 in
/-- **The target value, cellwise.**  `exp dwz63LogVal ^ (6 (n+1))` is the `alpha`-weighted product
of the fifteen cell values at the typical multiplicities.  This is
`dwz63_exp_logVal_pow_eq_prod` --- an *equality* --- read at the scale `t`. -/
theorem dwz63_expLogVal_pow_eq_cellProd {n t : ℕ} (hlen : n + 1 = 100000000 * t) :
    Real.exp dwz63LogVal ^ (6 * (n + 1))
      = ∏ c : Fin 15, dwz63Val c ^ (6 * (dwz63Alpha c * t)) := by
  have hexp : 6 * (n + 1) = 100000000 * (6 * t) := by omega
  rw [hexp, pow_mul, dwz63_exp_logVal_pow_eq_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  rw [← pow_mul]
  congr 1
  ring

set_option maxHeartbeats 1000000 in
/-- **The assembled weight dominates the endpoint's target.**

The three non-orbit-indexed factors match exactly; the three orbit cells are where the
comparison has content, and `dwz63_orbitFactor_le` settles them. -/
theorem dwz63_expLogVal_le_plainWeight {n t mb : ℕ} (hlen : n + 1 = 100000000 * t)
    (u : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) mb)
    (hmu : ∀ s : (cwSquarePartitionedTensor K dwz63Q).support,
      WordType.multiplicity (positiveWordEquiv _ mb u) s =
        if s.1 ∈ cwSquare112Orbit then 0 else dwz63AlphaAddress s.1 * t) :
    Real.exp dwz63LogVal ^ (6 * (n + 1))
      ≤ positiveSupportWordWeight (dwz63SymSixCellValue K) mb u
          * (dwz121LeafTerm K ^ (3 * (dwz63Alpha112 * t))) ^ 2
          * (dwz121LeafTerm K ^ (3 * (dwz63Alpha121 * t))) ^ 2
          * (dwz121LeafTerm K ^ (3 * (dwz63Alpha121 * t))) ^ 2 := by
  classical
  set f : Fin 15 → ℝ := fun c ↦ dwz63Val c ^ (6 * (dwz63Alpha c * t)) with hf
  set p : Fin 15 → Prop := fun c ↦ c = 6 ∨ c = 7 ∨ c = 10 with hp
  have hsplit : (∏ c ∈ Finset.univ.filter p, f c) * (∏ c ∈ Finset.univ.filter (¬ p ·), f c)
      = ∏ c : Fin 15, f c := Finset.prod_filter_mul_prod_filter_not _ _ _
  have horb : ∏ c ∈ Finset.univ.filter p, f c = f 6 * f 7 * f 10 := by
    rw [dwz63_filter_orbitIndices, Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    ring
  have hbulkSplit : ∏ c : Fin 15, dwz63BulkFactor t c
      = ∏ c ∈ Finset.univ.filter (¬ p ·), f c := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ p (dwz63BulkFactor t)]
    have hone : ∏ c ∈ Finset.univ.filter p, dwz63BulkFactor t c = 1 := by
      refine Finset.prod_eq_one fun c hc ↦ ?_
      have : p c := (Finset.mem_filter.mp hc).2
      rw [dwz63BulkFactor, if_pos this]
    rw [hone, one_mul]
    refine Finset.prod_congr rfl fun c hc ↦ ?_
    have : ¬ p c := (Finset.mem_filter.mp hc).2
    rw [dwz63BulkFactor, if_neg this]
  have hnonneg : 0 ≤ ∏ c ∈ Finset.univ.filter (¬ p ·), f c :=
    Finset.prod_nonneg fun c _ ↦ pow_nonneg (dwz63Val_pos c).le _
  rw [dwz63_bulkWeight_eq K u hmu, hbulkSplit, dwz63_expLogVal_pow_eq_cellProd hlen, ← hsplit,
    horb]
  calc f 6 * f 7 * f 10 * ∏ c ∈ Finset.univ.filter (¬ p ·), f c
      ≤ ((dwz121LeafTerm K ^ (3 * (dwz63Alpha112 * t))) ^ 2 *
          (dwz121LeafTerm K ^ (3 * (dwz63Alpha121 * t))) ^ 2 *
          (dwz121LeafTerm K ^ (3 * (dwz63Alpha121 * t))) ^ 2) *
          ∏ c ∈ Finset.univ.filter (¬ p ·), f c :=
        mul_le_mul_of_nonneg_right (dwz63_orbitFactor_le K t) hnonneg
    _ = (∏ c ∈ Finset.univ.filter (¬ p ·), f c) *
          (dwz121LeafTerm K ^ (3 * (dwz63Alpha112 * t))) ^ 2 *
          (dwz121LeafTerm K ^ (3 * (dwz63Alpha121 * t))) ^ 2 *
          (dwz121LeafTerm K ^ (3 * (dwz63Alpha121 * t))) ^ 2 := by ring


set_option maxHeartbeats 1000000 in
/-- **The endpoint's premise, in the shape the count lane consumes.**

`dwz63_symSix_weight_of_plainCopyCount` (`Examples/DuanWuZhouLevelTwoPlainCopyCount.lean`) asks
for `HasTauWeight K (symSix K leaf) dwz63Tau value` with `0 ≤ value`.  This supplies it at
`value = exp dwz63LogVal ^ (6 (n+1))`, so the composition needs no adaptation: `hvalue` is
`(pow_pos (Real.exp_pos _) _).le`, and the count lane's own copy bound then delivers the
endpoint's `6 N` exponent.

Everything below the surface is the plain route: `𝒯*` is a word over the fifteen coarse cells,
its three `(1,1,2)`-orbit letters are peeled into constant blocks valued by the `beta`-certificate
at the orbit maximum, `sym₆` is pushed onto the four blocks, and the comparison with the target
closes on `dwz63_exp_logVal_pow_eq_prod` plus `dwz63_logVal112_add_le_logVal121`. -/
theorem dwz63_hasTauWeight_symSix_plainLeaf_logVal {n t mb ka kb kc : ℕ}
    (q : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hcell : ∀ s : (cwSquarePartitionedTensor K dwz63Q).support, s.1 ∉ cwSquare112Orbit →
      HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent s.1) dwz63Tau
        (dwz63ValOf s.1))
    (hlen : n + 1 = 100000000 * t)
    (htyp : ∀ s : (cwSquarePartitionedTensor K dwz63Q).support,
      WordType.multiplicity (positiveWordEquiv _ n q) s = dwz63AlphaAddress s.1 * t)
    (hn : n = mb + ka + kb + kc + 3)
    (hka : ka + 1 = dwz63Alpha112 * t)
    (hkb : kb + 1 = dwz63Alpha121 * t)
    (hkc : kc + 1 = dwz63Alpha121 * t)
    (hwa : HasTauWeight K
      (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112))
        (ka + 1)) dwz63Tau ((dwz121LeafTerm K ^ (3 * (ka + 1))) ^ 2))
    (hwb : HasTauWeight K
      (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare121))
        (kb + 1)) dwz63Tau ((dwz121LeafTerm K ^ (3 * (kb + 1))) ^ 2))
    (hwc : HasTauWeight K
      (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare211))
        (kc + 1)) dwz63Tau ((dwz121LeafTerm K ^ (3 * (kc + 1))) ^ 2)) :
    HasTauWeight K
      (symSix K (PartitionedTensor.positiveSupportWordTensor
        (cwSquarePartitionedTensor K dwz63Q) n q)) dwz63Tau
      (Real.exp dwz63LogVal ^ (6 * (n + 1))) := by
  classical
  have h112 : cwSquare112 ∈ cwSquareSupport := by decide
  have h121 : cwSquare121 ∈ cwSquareSupport := by decide
  have h211 : cwSquare211 ∈ cwSquareSupport := by decide
  let sa : (cwSquarePartitionedTensor K dwz63Q).support := ⟨cwSquare112, h112⟩
  let sb : (cwSquarePartitionedTensor K dwz63Q).support := ⟨cwSquare121, h121⟩
  let sc : (cwSquarePartitionedTensor K dwz63Q).support := ⟨cwSquare211, h211⟩
  have hsaVal : (sa : CWSquareAddress) = cwSquare112 := rfl
  have hsbVal : (sb : CWSquareAddress) = cwSquare121 := rfl
  have hscVal : (sc : CWSquareAddress) = cwSquare211 := rfl
  have hab : sa ≠ sb := fun h ↦ by
    have := congrArg Subtype.val h
    rw [hsaVal, hsbVal] at this
    exact absurd this (by decide)
  have hac : sa ≠ sc := fun h ↦ by
    have := congrArg Subtype.val h
    rw [hsaVal, hscVal] at this
    exact absurd this (by decide)
  have hbc : sb ≠ sc := fun h ↦ by
    have := congrArg Subtype.val h
    rw [hsbVal, hscVal] at this
    exact absurd this (by decide)
  have hma : WordType.multiplicity (positiveWordEquiv _ n q) sa = ka + 1 := by
    rw [htyp sa, hsaVal, dwz63AlphaAddress_112, hka]
  have hmb : WordType.multiplicity (positiveWordEquiv _ n q) sb = kb + 1 := by
    rw [htyp sb, hsbVal, dwz63AlphaAddress_121, hkb]
  have hmc : WordType.multiplicity (positiveWordEquiv _ n q) sc = kc + 1 := by
    rw [htyp sc, hscVal, dwz63AlphaAddress_211, hkc]
  obtain ⟨u, hmult, hw⟩ := dwz63_hasTauWeight_symSix_plainLeaf K q hcell sa sb sc hab hac hbc
    hn hma hmb hmc (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) hwa hwb hwc
  -- the residual multiplicities of the bulk word
  have hmemA : (sa : CWSquareAddress) ∈ cwSquare112Orbit := by rw [hsaVal]; decide
  have hmemB : (sb : CWSquareAddress) ∈ cwSquare112Orbit := by rw [hsbVal]; decide
  have hmemC : (sc : CWSquareAddress) ∈ cwSquare112Orbit := by rw [hscVal]; decide
  have hmu : ∀ s : (cwSquarePartitionedTensor K dwz63Q).support,
      WordType.multiplicity (positiveWordEquiv _ mb u) s =
        if s.1 ∈ cwSquare112Orbit then 0 else dwz63AlphaAddress s.1 * t := by
    intro s
    have hm := hmult s
    by_cases hs : s.1 ∈ cwSquare112Orbit
    · rw [if_pos hs]
      simp only [cwSquare112Orbit, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with h | h | h
      · have hse : s = sa := Subtype.ext (h.trans hsaVal.symm)
        rw [hse] at hm ⊢
        rw [if_pos rfl, if_neg hab, if_neg hac, hma] at hm
        omega
      · have hse : s = sb := Subtype.ext (h.trans hsbVal.symm)
        rw [hse] at hm ⊢
        rw [if_neg (Ne.symm hab), if_pos rfl, if_neg hbc, hmb] at hm
        omega
      · have hse : s = sc := Subtype.ext (h.trans hscVal.symm)
        rw [hse] at hm ⊢
        rw [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), if_pos rfl, hmc] at hm
        omega
    · rw [if_neg hs]
      have hna : s ≠ sa := fun h ↦ hs (by rw [h]; exact hmemA)
      have hnb : s ≠ sb := fun h ↦ hs (by rw [h]; exact hmemB)
      have hnc : s ≠ sc := fun h ↦ hs (by rw [h]; exact hmemC)
      rw [if_neg hna, if_neg hnb, if_neg hnc, htyp s] at hm
      omega
  refine hw.mono ?_
  rw [hka, hkb, hkc] at hw ⊢
  exact dwz63_expLogVal_le_plainWeight K hlen u hmu


end Closing




end Examples

end AlgebraicComplexity
