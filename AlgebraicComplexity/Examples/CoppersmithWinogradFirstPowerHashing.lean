/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.BehrendRate
import AlgebraicComplexity.Analysis.TernaryMultinomial
import AlgebraicComplexity.Combinatorics.ProgressionFree
import AlgebraicComplexity.Examples.CoppersmithWinogradHashEncoding
import AlgebraicComplexity.Examples.CoppersmithWinogradPartition
import AlgebraicComplexity.MatrixMultiplication.AsymptoticSum
import AlgebraicComplexity.MatrixMultiplication.PartitionedPowerSelection
import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeExtraction
import AlgebraicComplexity.Tensor.TypeExtraction
import Mathlib.NumberTheory.Bertrand

/-!
# Full first-power Coppersmith--Winograd extraction

This module formalizes the classical six-constituent type selection for `CW_q`.  It fixes the
rational type used by the checked `q = 6` client, proves exact joint and marginal type counts,
performs semantic variable zeroing, applies progression-free hashing, and feeds the resulting
direct sum of square matrix-multiplication tensors to Schönhage's asymptotic sum inequality.

The theorem sequence follows Theorem 4.2 of
[He and Williams's CS 6810 notes](https://www.cs.cornell.edu/courses/cs6810/2023fa/Matrix.pdf),
with finite field sizes, type-class losses, and limiting arguments made explicit.

The final theorem removes all polynomial, prime-modulus, and Behrend losses through the reusable
subexponential-rate API.  The module deliberately does not import the numerical first-power
client, so the tensor/combinatorics layer remains reusable and the dependency graph stays
acyclic.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

/-- Counts of each corner and middle constituent in the rational CW6 type. -/
def cwFirstPowerAddressCount (k : ℕ) (s : CWBlockAddress) : ℕ :=
  match s .X, s .Y, s .Z with
  | .last, .zero, .zero
  | .zero, .last, .zero
  | .zero, .zero, .last => 481 * k
  | _, _, _ => 9519 * k

def cwFirstPowerNaturalType (k : ℕ) : cwBlockSupport → ℕ :=
  fun s ↦ cwFirstPowerAddressCount k s.1

def cwFirstPowerDepth (k : ℕ) : ℕ := 30000 * k - 1

theorem cwFirstPowerDepth_add_one {k : ℕ} (hk : 0 < k) :
    cwFirstPowerDepth k + 1 = 30000 * k := by
  unfold cwFirstPowerDepth
  omega

theorem cwFirstPowerNaturalType_mem_types {k : ℕ} (hk : 0 < k) :
    cwFirstPowerNaturalType k ∈
      WordType.types cwBlockSupport (cwFirstPowerDepth k + 1) := by
  rw [WordType.mem_types]
  change (∑ s : cwBlockSupport, cwFirstPowerAddressCount k s.1) = _
  calc
    (∑ s : cwBlockSupport, cwFirstPowerAddressCount k s.1) =
        ∑ s ∈ cwBlockSupport, cwFirstPowerAddressCount k s :=
      (Finset.sum_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (cwFirstPowerAddressCount k)).symm
    _ = 30000 * k := by
      rw [sum_cwBlockSupport]
      simp [cwFirstPowerAddressCount, cw200, cw020, cw002, cw011, cw101,
        cw110, cwBlockAddress]
      ring
    _ = cwFirstPowerDepth k + 1 := (cwFirstPowerDepth_add_one hk).symm

noncomputable def cwFirstPowerWords (k : ℕ) :
    Finset (PositiveWord cwBlockSupport (cwFirstPowerDepth k)) :=
  positiveTypeClass cwBlockSupport (cwFirstPowerDepth k) (cwFirstPowerNaturalType k)

def cwFirstPowerMarginalType (k : ℕ) : CWBlock → ℕ
  | .zero => 10481 * k
  | .middle => 19038 * k
  | .last => 481 * k

abbrev cw200S : cwBlockSupport := ⟨cw200, by decide⟩
abbrev cw020S : cwBlockSupport := ⟨cw020, by decide⟩
abbrev cw002S : cwBlockSupport := ⟨cw002, by decide⟩
abbrev cw011S : cwBlockSupport := ⟨cw011, by decide⟩
abbrev cw101S : cwBlockSupport := ⟨cw101, by decide⟩
abbrev cw110S : cwBlockSupport := ⟨cw110, by decide⟩

def cwNaturalMarginal (a : cwBlockSupport → ℕ) : Leg → CWBlock → ℕ
  | .X, .zero => a cw020S + a cw002S + a cw011S
  | .X, .middle => a cw101S + a cw110S
  | .X, .last => a cw200S
  | .Y, .zero => a cw200S + a cw002S + a cw101S
  | .Y, .middle => a cw011S + a cw110S
  | .Y, .last => a cw020S
  | .Z, .zero => a cw200S + a cw020S + a cw110S
  | .Z, .middle => a cw011S + a cw101S
  | .Z, .last => a cw002S

theorem cw_mappedType_eq_naturalMarginal (a : cwBlockSupport → ℕ)
    (c : Leg) (b : CWBlock) :
    WordType.mappedType (fun s : cwBlockSupport ↦ s.1 c) a b =
      cwNaturalMarginal a c b := by
  unfold WordType.mappedType WordType.letterFiber
  simp only [Finset.sum_filter]
  change (∑ s : cwBlockSupport, if s.1 c = b then a s else 0) = _
  rw [show (Finset.univ : Finset cwBlockSupport) =
    {cw200S, cw020S, cw002S, cw011S, cw101S, cw110S} by decide]
  rw [Finset.sum_insert (by decide : cw200S ∉
      ({cw020S, cw002S, cw011S, cw101S, cw110S} : Finset cwBlockSupport)),
    Finset.sum_insert (by decide : cw020S ∉
      ({cw002S, cw011S, cw101S, cw110S} : Finset cwBlockSupport)),
    Finset.sum_insert (by decide : cw002S ∉
      ({cw011S, cw101S, cw110S} : Finset cwBlockSupport)),
    Finset.sum_insert (by decide : cw011S ∉
      ({cw101S, cw110S} : Finset cwBlockSupport)),
    Finset.sum_insert (by decide : cw101S ∉
      ({cw110S} : Finset cwBlockSupport)), Finset.sum_singleton]
  cases c <;> cases b <;>
    simp [cwNaturalMarginal, cw200, cw020, cw002, cw011, cw101, cw110,
      cwBlockAddress, cw200S, cw020S, cw002S, cw011S, cw101S, cw110S,
      add_assoc]

theorem cwFirstPowerNaturalType_unique_of_mappedTypes (k : ℕ)
    (a : cwBlockSupport → ℕ)
    (h : ∀ c, WordType.mappedType (fun s : cwBlockSupport ↦ s.1 c) a =
      cwFirstPowerMarginalType k) :
    a = cwFirstPowerNaturalType k := by
  have hXlast := congrFun (h .X) .last
  have hYlast := congrFun (h .Y) .last
  have hZlast := congrFun (h .Z) .last
  have hXmiddle := congrFun (h .X) .middle
  have hYmiddle := congrFun (h .Y) .middle
  have hZmiddle := congrFun (h .Z) .middle
  rw [cw_mappedType_eq_naturalMarginal] at hXlast hYlast hZlast
  rw [cw_mappedType_eq_naturalMarginal] at hXmiddle hYmiddle hZmiddle
  simp only [cwNaturalMarginal, cwFirstPowerMarginalType] at hXlast hYlast hZlast
  simp only [cwNaturalMarginal, cwFirstPowerMarginalType] at hXmiddle hYmiddle hZmiddle
  funext s
  rcases s with ⟨s, hs⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [cwFirstPowerNaturalType, cwFirstPowerAddressCount, cw200, cwBlockAddress,
      cw200S] using hXlast
  · simpa [cwFirstPowerNaturalType, cwFirstPowerAddressCount, cw020, cwBlockAddress,
      cw020S] using hYlast
  · simpa [cwFirstPowerNaturalType, cwFirstPowerAddressCount, cw002, cwBlockAddress,
      cw002S] using hZlast
  · change a cw011S = 9519 * k
    omega
  · change a cw101S = 9519 * k
    omega
  · change a cw110S = 9519 * k
    omega

theorem cwFirstPowerMarginalType_mem_types {k : ℕ} (hk : 0 < k) :
    cwFirstPowerMarginalType k ∈
      WordType.types CWBlock (cwFirstPowerDepth k + 1) := by
  rw [WordType.mem_types, sum_cwBlock]
  simp [cwFirstPowerMarginalType, cwFirstPowerDepth_add_one hk]
  ring

theorem cwFirstPower_mappedType (k : ℕ) (c : Leg) (b : CWBlock) :
    WordType.mappedType (fun s : cwBlockSupport ↦ s.1 c)
        (cwFirstPowerNaturalType k) b =
      match b with
      | .zero => 10481 * k
      | .middle => 19038 * k
      | .last => 481 * k := by
  unfold WordType.mappedType WordType.letterFiber cwFirstPowerNaturalType
  simp only [Finset.sum_filter]
  change (∑ s : cwBlockSupport,
    if s.1 c = b then cwFirstPowerAddressCount k s.1 else 0) = _
  calc
    (∑ s : cwBlockSupport,
      if s.1 c = b then cwFirstPowerAddressCount k s.1 else 0) =
        ∑ s ∈ cwBlockSupport,
          if s c = b then cwFirstPowerAddressCount k s else 0 :=
      (Finset.sum_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ if s c = b then cwFirstPowerAddressCount k s else 0)).symm
    _ = _ := by
      rw [sum_cwBlockSupport]
      cases c <;> cases b <;>
        simp [cwFirstPowerAddressCount, cw200, cw020, cw002, cw011, cw101,
          cw110, cwBlockAddress] <;> ring

theorem cwFirstPower_mappedType_eq (k : ℕ) (c : Leg) :
    WordType.mappedType (fun s : cwBlockSupport ↦ s.1 c)
        (cwFirstPowerNaturalType k) = cwFirstPowerMarginalType k := by
  funext b
  rw [cwFirstPower_mappedType]
  cases b <;> rfl

theorem cwFirstPowerMarginal_multinomial_eq_ternary (k : ℕ) :
    Nat.multinomial Finset.univ (cwFirstPowerMarginalType k) =
      WordType.ternaryMultinomial (10481 * k) (19038 * k) (481 * k) := by
  have hcw : (Finset.univ : Finset CWBlock) = {.zero, .middle, .last} := by decide
  have hfin : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  unfold WordType.ternaryMultinomial Nat.multinomial
  rw [hcw, hfin]
  simp [cwFirstPowerMarginalType, WordType.ternaryCounts]

theorem card_cwFirstPowerMarginalTypeClass {k : ℕ} (hk : 0 < k) :
    (WordType.typeClass (cwFirstPowerDepth k + 1)
      (cwFirstPowerMarginalType k)).card =
        WordType.ternaryMultinomial (10481 * k) (19038 * k) (481 * k) := by
  rw [WordType.card_typeClass_eq_multinomial _
    (cwFirstPowerMarginalType_mem_types hk),
    cwFirstPowerMarginal_multinomial_eq_ternary]

noncomputable def cwFirstPowerTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (k : ℕ) :
    Finset (ProgressionHash.LegalTriple R (Fin (cwFirstPowerDepth k + 1)) 2) :=
  (cwPartitionHashEncoding (R := R)).legalTargets
    (cwFirstPowerDepth k) (cwFirstPowerWords k)

@[simp] theorem card_cwFirstPowerTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (k : ℕ) :
    (cwFirstPowerTargets (R := R) k).card = (cwFirstPowerWords k).card := by
  exact PartitionHashEncoding.card_legalTargets _ _ _

theorem cwFirstPowerLegWord_mem_marginalTypeClass
    (k : ℕ) (q : PositiveWord cwBlockSupport (cwFirstPowerDepth k))
    (hq : q ∈ cwFirstPowerWords k) (c : Leg) :
    positiveWordEquiv CWBlock (cwFirstPowerDepth k)
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          (cwFirstPowerDepth k) q c) ∈
      WordType.typeClass (cwFirstPowerDepth k + 1)
        (cwFirstPowerMarginalType k) := by
  rw [WordType.mem_typeClass]
  rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
    (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)]
  change WordType.multiplicity
    ((fun s : cwBlockSupport ↦ s.1 c) ∘
      positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) q) = _
  rw [WordType.multiplicity_comp_eq_mappedType,
    mem_positiveTypeClass.mp hq, cwFirstPower_mappedType_eq]

noncomputable def cwFirstPowerFiberSize (k : ℕ) : ℕ :=
  (cwFirstPowerWords k).card /
    (WordType.typeClass (cwFirstPowerDepth k + 1)
      (cwFirstPowerMarginalType k)).card

theorem cwFirstPowerWords_nonempty {k : ℕ} (hk : 0 < k) :
    (cwFirstPowerWords k).Nonempty := by
  rw [← Finset.card_pos]
  change 0 < (positiveTypeClass cwBlockSupport (cwFirstPowerDepth k)
    (cwFirstPowerNaturalType k)).card
  rw [card_positiveTypeClass]
  exact Finset.card_pos.mpr
    (WordType.typeClass_nonempty _ (cwFirstPowerNaturalType_mem_types hk))

theorem cwFirstPowerMarginalCard_mul_fiberSize {k : ℕ} (hk : 0 < k) :
    (WordType.typeClass (cwFirstPowerDepth k + 1)
        (cwFirstPowerMarginalType k)).card * cwFirstPowerFiberSize k =
      (cwFirstPowerWords k).card := by
  unfold cwFirstPowerFiberSize
  exact Nat.mul_div_cancel'
    (by
      obtain ⟨q, hq⟩ := cwFirstPowerWords_nonempty hk
      let target := (fun s : cwBlockSupport ↦ s.1 .X) ∘
        positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) q
      have htarget : target ∈ WordType.typeClass (cwFirstPowerDepth k + 1)
          (cwFirstPowerMarginalType k) := by
        rw [WordType.mem_typeClass]
        change WordType.multiplicity
          ((fun s : cwBlockSupport ↦ s.1 .X) ∘
            positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) q) = _
        rw [WordType.multiplicity_comp_eq_mappedType,
          mem_positiveTypeClass.mp hq, cwFirstPower_mappedType_eq]
      have hdouble := WordType.card_targetType_mul_card_typedWordMapFiber
        (fun s : cwBlockSupport ↦ s.1 .X) (cwFirstPowerNaturalType k) target
        (by rwa [cwFirstPower_mappedType_eq])
      have hsource :
          (WordType.typeClass (cwFirstPowerDepth k + 1)
            (cwFirstPowerNaturalType k)).card = (cwFirstPowerWords k).card :=
        (card_positiveTypeClass (I := cwBlockSupport) (cwFirstPowerDepth k)
          (cwFirstPowerNaturalType k)).symm
      rw [cwFirstPower_mappedType_eq, hsource] at hdouble
      exact ⟨_, hdouble.symm⟩)

theorem cwFirstPowerFiberSize_pos {k : ℕ} (hk : 0 < k) :
    0 < cwFirstPowerFiberSize k := by
  have hsource := Finset.card_pos.mpr (cwFirstPowerWords_nonempty hk)
  have hproduct := cwFirstPowerMarginalCard_mul_fiberSize hk
  apply pos_of_mul_pos_right (show 0 <
    (WordType.typeClass (cwFirstPowerDepth k + 1)
      (cwFirstPowerMarginalType k)).card * cwFirstPowerFiberSize k by
      rwa [hproduct])
  exact Nat.zero_le _

theorem fintypeCard_cwBlockSupport : Fintype.card cwBlockSupport = 6 := by
  rw [Fintype.card_coe]
  decide

theorem card_cwFirstPowerWords_le {k : ℕ} (hk : 0 < k) :
    (cwFirstPowerWords k).card ≤ 6 ^ (30000 * k) := by
  calc
    (cwFirstPowerWords k).card ≤
        Fintype.card (PositiveWord cwBlockSupport (cwFirstPowerDepth k)) :=
      Finset.card_le_univ _
    _ = Fintype.card (Fin (cwFirstPowerDepth k + 1) → cwBlockSupport) :=
      Fintype.card_congr (positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k))
    _ = Fintype.card cwBlockSupport ^ (cwFirstPowerDepth k + 1) := by
      rw [Fintype.card_fun, Fintype.card_fin]
    _ = 6 ^ (30000 * k) := by
      rw [fintypeCard_cwBlockSupport, cwFirstPowerDepth_add_one hk]

theorem cwFirstPowerFiberSize_le_words (k : ℕ) :
    cwFirstPowerFiberSize k ≤ (cwFirstPowerWords k).card := by
  unfold cwFirstPowerFiberSize
  exact Nat.div_le_self _ _

theorem card_cwFirstPowerTypedWordMapFiber {k : ℕ} (hk : 0 < k)
    (c : Leg) (target : Fin (cwFirstPowerDepth k + 1) → CWBlock)
    (htarget : target ∈ WordType.typeClass (cwFirstPowerDepth k + 1)
      (cwFirstPowerMarginalType k)) :
    (WordType.typedWordMapFiber (fun s : cwBlockSupport ↦ s.1 c)
      (cwFirstPowerNaturalType k) target).card = cwFirstPowerFiberSize k := by
  have hdouble := WordType.card_targetType_mul_card_typedWordMapFiber
    (fun s : cwBlockSupport ↦ s.1 c) (cwFirstPowerNaturalType k) target
    (by rwa [cwFirstPower_mappedType_eq])
  have hsource :
      (WordType.typeClass (cwFirstPowerDepth k + 1)
        (cwFirstPowerNaturalType k)).card = (cwFirstPowerWords k).card := by
    exact (card_positiveTypeClass (I := cwBlockSupport) (cwFirstPowerDepth k)
      (cwFirstPowerNaturalType k)).symm
  rw [cwFirstPower_mappedType_eq, hsource] at hdouble
  unfold cwFirstPowerFiberSize
  exact Nat.eq_div_of_mul_eq_left
    (Finset.card_ne_zero.mpr
      (WordType.typeClass_nonempty _ (cwFirstPowerMarginalType_mem_types hk)))
    (by simpa [Nat.mul_comm] using hdouble)

theorem card_cwFirstPowerTarget_legFiber_le
    {R : Type*} [Field R] [NeZero (2 : R)] {k : ℕ} (hk : 0 < k)
    {triple : ProgressionHash.LegalTriple R (Fin (cwFirstPowerDepth k + 1)) 2}
    (htriple : triple ∈ cwFirstPowerTargets (R := R) k) (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber
      (cwFirstPowerTargets (R := R) k) triple c).card ≤
        cwFirstPowerFiberSize k := by
  classical
  change triple ∈ (cwFirstPowerWords k).image
    ((cwPartitionHashEncoding (R := R)).legalTriple (cwFirstPowerDepth k)) at htriple
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp htriple
  have hlegal : (cwPartitionHashEncoding (R := R)).legalTriple
      (cwFirstPowerDepth k) q ∈ cwFirstPowerTargets (R := R) k := by
    unfold cwFirstPowerTargets PartitionHashEncoding.legalTargets
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  apply ((cwPartitionHashEncoding (R := R)).card_legFiber_legalTargets_le_card_typedWordMapFiber
    (cwFirstPowerDepth k) (cwFirstPowerWords k) (cwFirstPowerNaturalType k)
    (fun word hword ↦ mem_positiveTypeClass.mp hword) hlegal c).trans_eq
  exact card_cwFirstPowerTypedWordMapFiber hk c _
    (by simpa using cwFirstPowerLegWord_mem_marginalTypeClass k q hq c)

theorem card_cwFirstPowerTarget_legwiseCompetitors_le
    {R : Type*} [Field R] [NeZero (2 : R)] {k : ℕ} (hk : 0 < k)
    {triple : ProgressionHash.LegalTriple R (Fin (cwFirstPowerDepth k + 1)) 2}
    (htriple : triple ∈ cwFirstPowerTargets (R := R) k) :
    (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
      (cwFirstPowerTargets (R := R) k) triple).card ≤
        3 * cwFirstPowerFiberSize k := by
  apply ProgressionHash.LegalTriple.card_legwiseCompetitorYIndices_le_three_mul
  intro c
  exact card_cwFirstPowerTarget_legFiber_le hk htriple c

noncomputable def cwFirstPowerKeepBlock (k : ℕ) (_c : Leg)
    (word : PositiveWord CWBlock (cwFirstPowerDepth k)) : Prop :=
  WordType.multiplicity
    (positiveWordEquiv CWBlock (cwFirstPowerDepth k) word) =
      cwFirstPowerMarginalType k

noncomputable instance cwFirstPowerKeepBlock_decidable (k : ℕ) (c : Leg)
    (word : PositiveWord CWBlock (cwFirstPowerDepth k)) :
    Decidable (cwFirstPowerKeepBlock k c word) := by
  classical
  unfold cwFirstPowerKeepBlock
  infer_instance

theorem mem_cwFirstPowerWords_iff_keepBlocks (k : ℕ)
    (q : PositiveWord cwBlockSupport (cwFirstPowerDepth k)) :
    q ∈ cwFirstPowerWords k ↔
      ∀ c, cwFirstPowerKeepBlock k c
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          (cwFirstPowerDepth k) q c) := by
  constructor
  · intro hq c
    exact WordType.mem_typeClass.mp
      (cwFirstPowerLegWord_mem_marginalTypeClass k q hq c)
  · intro hkeep
    rw [cwFirstPowerWords, mem_positiveTypeClass]
    apply cwFirstPowerNaturalType_unique_of_mappedTypes k
    intro c
    have hc := hkeep c
    unfold cwFirstPowerKeepBlock at hc
    rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)] at hc
    change WordType.multiplicity
      ((fun s : cwBlockSupport ↦ s.1 c) ∘
        positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) q) = _ at hc
    rwa [WordType.multiplicity_comp_eq_mappedType] at hc

section TensorPower

universe u

variable (K : Type u) [CommRing K]
variable (q k : ℕ)

abbrev cwTensorConstituentM (s : (cwPartitionedTensor K q).support) : ℕ :=
  (cwConstituentDimensions q s.1).1

abbrev cwTensorConstituentN (s : (cwPartitionedTensor K q).support) : ℕ :=
  (cwConstituentDimensions q s.1).2.1

abbrev cwTensorConstituentP (s : (cwPartitionedTensor K q).support) : ℕ :=
  (cwConstituentDimensions q s.1).2.2

theorem cwFirstPower_positiveWordProduct_m
    (word : PositiveWord (cwPartitionedTensor K q).support (cwFirstPowerDepth k))
    (hword : word ∈ positiveTypeClass (cwPartitionedTensor K q).support
      (cwFirstPowerDepth k) (cwFirstPowerNaturalType k)) :
    positiveWordProduct (cwTensorConstituentM K q)
      (cwFirstPowerDepth k) word = q ^ (9519 * k) := by
  rw [positiveWordProduct_eq_prod_pow (a := cwFirstPowerNaturalType k)
    (cwTensorConstituentM K q) hword]
  change (∏ s : cwBlockSupport,
    (cwConstituentDimensions q s.1).1 ^ cwFirstPowerNaturalType k s) = _
  calc
    _ = ∏ s ∈ cwBlockSupport,
        (cwConstituentDimensions q s).1 ^ cwFirstPowerAddressCount k s :=
      (Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).1 ^
          cwFirstPowerAddressCount k s)).symm
    _ = _ := by
      rw [prod_cwBlockSupport]
      simp [cwConstituentDimensions, cwFirstPowerAddressCount,
        cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

theorem cwFirstPower_positiveWordProduct_n
    (word : PositiveWord (cwPartitionedTensor K q).support (cwFirstPowerDepth k))
    (hword : word ∈ positiveTypeClass (cwPartitionedTensor K q).support
      (cwFirstPowerDepth k) (cwFirstPowerNaturalType k)) :
    positiveWordProduct (cwTensorConstituentN K q)
      (cwFirstPowerDepth k) word = q ^ (9519 * k) := by
  rw [positiveWordProduct_eq_prod_pow (a := cwFirstPowerNaturalType k)
    (cwTensorConstituentN K q) hword]
  change (∏ s : cwBlockSupport,
    (cwConstituentDimensions q s.1).2.1 ^ cwFirstPowerNaturalType k s) = _
  calc
    _ = ∏ s ∈ cwBlockSupport,
        (cwConstituentDimensions q s).2.1 ^ cwFirstPowerAddressCount k s :=
      (Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).2.1 ^
          cwFirstPowerAddressCount k s)).symm
    _ = _ := by
      rw [prod_cwBlockSupport]
      simp [cwConstituentDimensions, cwFirstPowerAddressCount,
        cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

theorem cwFirstPower_positiveWordProduct_p
    (word : PositiveWord (cwPartitionedTensor K q).support (cwFirstPowerDepth k))
    (hword : word ∈ positiveTypeClass (cwPartitionedTensor K q).support
      (cwFirstPowerDepth k) (cwFirstPowerNaturalType k)) :
    positiveWordProduct (cwTensorConstituentP K q)
      (cwFirstPowerDepth k) word = q ^ (9519 * k) := by
  rw [positiveWordProduct_eq_prod_pow (a := cwFirstPowerNaturalType k)
    (cwTensorConstituentP K q) hword]
  change (∏ s : cwBlockSupport,
    (cwConstituentDimensions q s.1).2.2 ^ cwFirstPowerNaturalType k s) = _
  calc
    _ = ∏ s ∈ cwBlockSupport,
        (cwConstituentDimensions q s).2.2 ^ cwFirstPowerAddressCount k s :=
      (Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).2.2 ^
          cwFirstPowerAddressCount k s)).symm
    _ = _ := by
      rw [prod_cwBlockSupport]
      simp [cwConstituentDimensions, cwFirstPowerAddressCount,
        cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

noncomputable def cwFirstPowerPartitionedPower :
    PartitionedTensor (K := K)
      (A := fun _ ↦ PositiveWord CWBlock (cwFirstPowerDepth k))
      (PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
        (cwFirstPowerDepth k)) :=
  ((cwPartitionedTensor K q).positivePower (cwFirstPowerDepth k)).select
    (cwFirstPowerKeepBlock k)

theorem cwFirstPowerPartitionedPower_support
    {R : Type*} [Field R] [NeZero (2 : R)] :
    (cwFirstPowerPartitionedPower K q k).support =
      (cwPartitionHashEncoding (R := R)).modeledAddresses
        (cwFirstPowerDepth k) (cwFirstPowerTargets (R := R) k) := by
  classical
  unfold cwFirstPowerPartitionedPower cwFirstPowerTargets
  exact PartitionHashEncoding.select_positivePower_support
    (cwPartitionedTensor K q) (cwPartitionHashEncoding (R := R))
    (cwFirstPowerDepth k) (cwFirstPowerKeepBlock k) (cwFirstPowerWords k)
    (mem_cwFirstPowerWords_iff_keepBlocks k)

theorem cwFirstPowerPartitionedPower_constituent_restricts_square
    (s : (cwFirstPowerPartitionedPower K q k).support) :
    Restricts ((cwFirstPowerPartitionedPower K q k).constituent s.1)
      (matrixMultiplication (K := K)
        (q ^ (9519 * k)) (q ^ (9519 * k)) (q ^ (9519 * k))) := by
  refine Tensor.Restricts.select_positivePower_constituent
    (cwPartitionedTensor K q) (cwFirstPowerDepth k) (cwFirstPowerKeepBlock k)
    (cwFirstPowerWords k) (mem_cwFirstPowerWords_iff_keepBlocks k) ?_ s
  intro word hword
  have hwordTensor : word ∈ positiveTypeClass
      (cwPartitionedTensor K q).support (cwFirstPowerDepth k)
        (cwFirstPowerNaturalType k) := hword
  have hrestrict := Tensor.Restricts.positiveSupportWordTensor_matrixMultiplication
    (cwPartitionedTensor K q)
    (cwTensorConstituentM K q) (cwTensorConstituentN K q)
    (cwTensorConstituentP K q)
    (cwSupportedConstituent_restricts K q)
    (cwFirstPowerDepth k) word
  rwa [cwFirstPower_positiveWordProduct_m K q k word hwordTensor,
    cwFirstPower_positiveWordProduct_n K q k word hwordTensor,
    cwFirstPower_positiveWordProduct_p K q k word hwordTensor] at hrestrict

theorem cwPower_restricts_firstPowerPartitionedPower :
    Restricts
      (Tensor.power (cwPartitionedTensor K q).realize (cwFirstPowerDepth k + 1))
      (cwFirstPowerPartitionedPower K q k).realize := by
  exact (Tensor.Restricts.power_partitionedPositivePower
      (cwPartitionedTensor K q) (cwFirstPowerDepth k)).trans
    (Tensor.Restricts.partitionedSelect
      ((cwPartitionedTensor K q).positivePower (cwFirstPowerDepth k))
      (cwFirstPowerKeepBlock k))

theorem cwPower_restricts_legwiseIsolatedIndexedDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwFirstPowerDepth k + 1))) :
    Restricts
      (Tensor.power (cwPartitionedTensor K q).realize (cwFirstPowerDepth k + 1))
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
            (cwFirstPowerDepth k))
          ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed))
        (fun s : (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed ↦
          (cwFirstPowerPartitionedPower K q k).constituent s.1)) := by
  apply (cwPower_restricts_firstPowerPartitionedPower K q k).trans
  apply Tensor.Restricts.modeledTargets_to_legwiseIsolatedIndexedDirectSum
    (cwPartitionHashEncoding (R := R)) (cwFirstPowerWords k) B hB seed
      (cwFirstPowerPartitionedPower K q k)
  exact cwFirstPowerPartitionedPower_support K q k

theorem cwLegwiseIsolatedIndexedDirectSum_restricts_squareDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (cwFirstPowerDepth k + 1))) :
    Restricts
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
            (cwFirstPowerDepth k))
          ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed))
        (fun s : (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed ↦
          (cwFirstPowerPartitionedPower K q k).constituent s.1))
      (matrixMultiplicationDirectSum
        (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
          (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed)
        K (fun _ ↦ q ^ (9519 * k)) (fun _ ↦ q ^ (9519 * k))
          (fun _ ↦ q ^ (9519 * k))) :=
  Tensor.Restricts.legwiseIsolatedIndexedDirectSum_const
    (cwPartitionHashEncoding (R := R)) (cwFirstPowerWords k) B seed
    (cwFirstPowerPartitionedPower K q k)
    (cwFirstPowerPartitionedPower_support (R := R) K q k)
    (cwFirstPowerPartitionedPower_constituent_restricts_square K q k)

theorem cwPower_restricts_legwiseIsolatedSquareDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwFirstPowerDepth k + 1))) :
    Restricts
      (Tensor.power (cwPartitionedTensor K q).realize (cwFirstPowerDepth k + 1))
      (matrixMultiplicationDirectSum
        (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
          (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed)
        K (fun _ ↦ q ^ (9519 * k)) (fun _ ↦ q ^ (9519 * k))
          (fun _ ↦ q ^ (9519 * k))) :=
  (cwPower_restricts_legwiseIsolatedIndexedDirectSum K q k B hB seed).trans
    (cwLegwiseIsolatedIndexedDirectSum_restricts_squareDirectSum K q k B seed)

theorem cwFirstPower_competitorQuarter_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (hk : 0 < k) (hcard : 12 * cwFirstPowerFiberSize k ≤ Fintype.card R) :
    ∀ triple ∈ cwFirstPowerTargets (R := R) k,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (cwFirstPowerTargets (R := R) k) triple).card ≤ Fintype.card R := by
  intro triple htriple
  calc
    4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (cwFirstPowerTargets (R := R) k) triple).card ≤
        4 * (3 * cwFirstPowerFiberSize k) :=
      Nat.mul_le_mul_left 4
        (card_cwFirstPowerTarget_legwiseCompetitors_le hk htriple)
    _ = 12 * cwFirstPowerFiberSize k := by ring
    _ ≤ Fintype.card R := hcard

theorem exists_cwPower_squareExtraction
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ cwFirstPowerTargets (R := R) k,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (cwFirstPowerTargets (R := R) k) triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (cwFirstPowerDepth k + 1)),
      3 * (cwFirstPowerWords k).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed).card ∧
        Restricts
          (Tensor.power (cwPartitionedTensor K q).realize
            (cwFirstPowerDepth k + 1))
          (matrixMultiplicationDirectSum
            (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed)
            K (fun _ ↦ q ^ (9519 * k)) (fun _ ↦ q ^ (9519 * k))
              (fun _ ↦ q ^ (9519 * k))) := by
  obtain ⟨seed, hcount, _hsubset, _hinjective⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_legwiseIsolatedTargets
      (cwFirstPowerTargets (R := R) k) B hB hquarter
  refine ⟨seed, ?_, cwPower_restricts_legwiseIsolatedSquareDirectSum K q k B hB seed⟩
  rw [(cwPartitionHashEncoding (R := R)).card_legwiseIsolatedPowerAddresses
    (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed]
  change 3 * ((cwPartitionHashEncoding (R := R)).legalTargets
      (cwFirstPowerDepth k) (cwFirstPowerWords k)).card * B.card ≤ _ at hcount
  rw [PartitionHashEncoding.card_legalTargets] at hcount
  exact hcount

theorem exists_cwPower_squareExtraction_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (hk : 0 < k) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hcard : 12 * cwFirstPowerFiberSize k ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (cwFirstPowerDepth k + 1)),
      3 * (cwFirstPowerWords k).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed).card ∧
        Restricts
          (Tensor.power (cwPartitionedTensor K q).realize
            (cwFirstPowerDepth k + 1))
          (matrixMultiplicationDirectSum
            (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed)
            K (fun _ ↦ q ^ (9519 * k)) (fun _ ↦ q ^ (9519 * k))
              (fun _ ↦ q ^ (9519 * k))) :=
  exists_cwPower_squareExtraction K q k B hB
    (cwFirstPower_competitorQuarter_of_fieldCard k hk hcard)

end TensorPower

section FiniteAsymptoticSum

variable (K : Type u) [Field K]
variable (q k : ℕ)

/-- Explicit subexponential loss in the full six-constituent CW extraction. -/
noncomputable def cwFirstPowerSubexponentialLoss (k : ℕ) : ℝ :=
  96 * WordType.ternaryMultinomialLoss 10481 19038 481 k *
    Real.exp (1700 * √((k + 1 : ℕ) : ℝ))

theorem cwFirstPowerSubexponentialLoss_subexponential :
    Growth.Subexponential cwFirstPowerSubexponentialLoss := by
  have h := Growth.Subexponential.const_mul_natCast_pow_mul_exp_sqrt_succ
    (c := 96 * (Real.exp 1) ^ 3 * (((10481 * 19038 * 481 : ℕ) : ℝ)))
    (a := (1700 : ℝ)) (by positivity) (by positivity) 3
  have heq : cwFirstPowerSubexponentialLoss = fun n : ℕ ↦
      (96 * (Real.exp 1) ^ 3 * (((10481 * 19038 * 481 : ℕ) : ℝ))) *
        (n : ℝ) ^ 3 * Real.exp (1700 * √((n + 1 : ℕ) : ℝ)) := by
    funext n
    unfold cwFirstPowerSubexponentialLoss WordType.ternaryMultinomialLoss
    ring
  rw [heq]
  exact h

/-- Normalize the full-CW square constituent volume in Schönhage's inequality.  This is the
generic identity `cubeVolume_rpow_omega_div_three` at the first-power schedule
`n = 9519 * k`. -/
theorem cwFirstPowerCubeVolume_rpow_omega_div_three (hq : 0 < q) :
    ((((q ^ (9519 * k)) * (q ^ (9519 * k)) * (q ^ (9519 * k)) : ℕ) : ℝ) ^
        (omega K / 3)) =
      (((q : ℝ) ^ omega K) ^ (9519 * k)) :=
  cubeVolume_rpow_omega_div_three K q (9519 * k) hq

/-- The finite full-CW/Schönhage inequality with all type-fiber competitor counting discharged. -/
theorem exists_cwPower_asymptoticSum_bound_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (hq : 0 < q) (hk : 0 < k)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hcard : 12 * cwFirstPowerFiberSize k ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (cwFirstPowerDepth k + 1)),
      3 * (cwFirstPowerWords k).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed).card ∧
        (((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed).card : ℝ) *
            (((q ^ (9519 * k)) * (q ^ (9519 * k)) * (q ^ (9519 * k)) : ℕ) : ℝ) ^
              (omega K / 3) ≤
          (((q + 2) ^ (cwFirstPowerDepth k + 1) : ℕ) : ℝ) := by
  obtain ⟨seed, hcount, hrestrict⟩ :=
    exists_cwPower_squareExtraction_of_fieldCard K q k hk B hB hcard
  refine ⟨seed, hcount, ?_⟩
  have hdeg := PolynomialDegenerates.of_restricts hrestrict
  have hasi := asymptoticSum_le_of_borderRankLE
    (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
      (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed)
    K (fun _ ↦ q ^ (9519 * k)) (fun _ ↦ q ^ (9519 * k))
      (fun _ ↦ q ^ (9519 * k))
    ((cwPartitionedTensor_borderRankLE K q).power (cwFirstPowerDepth k + 1))
    (fun _ ↦ pow_pos hq _) (fun _ ↦ pow_pos hq _) (fun _ ↦ pow_pos hq _)
    hdeg
  simpa only [asymptoticSum_const, Fintype.card_coe] using hasi

/-- Fully instantiated finite full-CW extraction over a prime cyclic field. -/
theorem exists_cwPower_asymptoticSum_bound_zmod (M : ℕ) [Fact M.Prime]
    (hq : 0 < q) (hk : 0 < k)
    (hcard : 12 * cwFirstPowerFiberSize k ≤ M) :
    ∃ B : Finset (ZMod M),
      B.card = rothNumberNat (M / 2) ∧ ThreeAPFree (B : Set (ZMod M)) ∧
      ∃ copies : ℕ,
        3 * (cwFirstPowerWords k).card * B.card ≤ 4 * (M * M) * copies ∧
          (copies : ℝ) *
              (((q ^ (9519 * k)) * (q ^ (9519 * k)) * (q ^ (9519 * k)) : ℕ) : ℝ) ^
                (omega K / 3) ≤
            (((q + 2) ^ (cwFirstPowerDepth k + 1) : ℕ) : ℝ) := by
  have hM : 3 ≤ M := by
    have hd := cwFirstPowerFiberSize_pos hk
    omega
  letI : NeZero (2 : ZMod M) := neZero_two_zmod_of_three_le hM
  obtain ⟨B, hBcard, hB⟩ := exists_threeAPFree_zmod_half M
  obtain ⟨seed, hcount, hasi⟩ :=
    exists_cwPower_asymptoticSum_bound_of_fieldCard K q k hq hk B hB (by
      simpa [ZMod.card] using hcard)
  let copies := ((cwPartitionHashEncoding (R := ZMod M)).legwiseIsolatedPowerAddresses
    (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed).card
  exact ⟨B, hBcard, hB, copies, by simpa [ZMod.card, copies] using hcount,
    by simpa [copies] using hasi⟩

/-- Purely numerical finite full-CW output after choosing the hashing modulus by Bertrand's
postulate. -/
theorem exists_prime_cwPower_asymptoticSum_bound (hq : 0 < q) (hk : 0 < k) :
    ∃ M copies : ℕ,
      M.Prime ∧
        12 * cwFirstPowerFiberSize k < M ∧
        M ≤ 24 * cwFirstPowerFiberSize k ∧
        3 * (cwFirstPowerWords k).card * rothNumberNat (M / 2) ≤
          4 * (M * M) * copies ∧
        (copies : ℝ) *
              (((q ^ (9519 * k)) * (q ^ (9519 * k)) * (q ^ (9519 * k)) : ℕ) : ℝ) ^
                (omega K / 3) ≤
          (((q + 2) ^ (cwFirstPowerDepth k + 1) : ℕ) : ℝ) := by
  have hn : 12 * cwFirstPowerFiberSize k ≠ 0 := by
    have := cwFirstPowerFiberSize_pos hk
    positivity
  obtain ⟨M, hprime, hlower, hupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (12 * cwFirstPowerFiberSize k) hn
  letI : Fact M.Prime := ⟨hprime⟩
  obtain ⟨B, hBcard, _hB, copies, hcopies, hasi⟩ :=
    exists_cwPower_asymptoticSum_bound_zmod K q k M hq hk hlower.le
  refine ⟨M, copies, hprime, hlower, ?_, ?_, hasi⟩
  · calc
      M ≤ 2 * (12 * cwFirstPowerFiberSize k) := hupper
      _ = 24 * cwFirstPowerFiberSize k := by ring
  · rwa [hBcard] at hcopies

/-- Every finite full-CW extraction satisfies the entropy-base rate inequality with only an
explicit subexponential loss. -/
theorem cwFirstPower_rate_inequality (hq : 0 < q) (hk : 0 < k) :
    ((WordType.ternaryEntropyBase 10481 19038 481 *
        (((q : ℝ) ^ omega K) ^ 9519)) ^ k) ≤
      cwFirstPowerSubexponentialLoss k *
        (((((q + 2 : ℕ) : ℝ) ^ 30000) ^ k)) := by
  obtain ⟨M, copies, _hprime, hlower, hupper, hcount, hasi⟩ :=
    exists_prime_cwPower_asymptoticSum_bound K q k hq hk
  let P := (WordType.typeClass (cwFirstPowerDepth k + 1)
    (cwFirstPowerMarginalType k)).card
  let d := cwFirstPowerFiberSize k
  let S := (cwFirstPowerWords k).card
  have hdPos : 0 < d := cwFirstPowerFiberSize_pos hk
  have hM : 3 ≤ M := by omega
  have hSPNat : P * d = S := by
    simpa [P, d, S] using cwFirstPowerMarginalCard_mul_fiberSize hk
  have hSP : (P : ℝ) * (d : ℝ) = (S : ℝ) := by exact_mod_cast hSPNat
  have hdUpper : d ≤ 6 ^ (30000 * k) :=
    (cwFirstPowerFiberSize_le_words k).trans (card_cwFirstPowerWords_le hk)
  have hMupperSix : M ≤ 24 * 6 ^ (30000 * k) :=
    hupper.trans (Nat.mul_le_mul_left 24 hdUpper)
  have hhalfPos : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) := by
    have hpos : 0 < M / 2 := by omega
    exact_mod_cast hpos
  have hhalfUpper : ((M / 2 : ℕ) : ℝ) ≤ 12 * (6 : ℝ) ^ (30000 * k) := by
    have hnat : M / 2 ≤ 12 * 6 ^ (30000 * k) := by omega
    calc
      ((M / 2 : ℕ) : ℝ) ≤ ((12 * 6 ^ (30000 * k) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = 12 * (6 : ℝ) ^ (30000 * k) := by push_cast; ring
  have hsqrt := Growth.sqrt_log_le_mul_sqrt_succ (x := ((M / 2 : ℕ) : ℝ)) (c := 12)
    (G := 6) (s := 425) (m := 30000) (k := k) hhalfPos (by norm_num) (by norm_num)
    (by norm_num) hhalfUpper (by norm_num) (by norm_num)
  have ht : 4 * √(Real.log ((M / 2 : ℕ) : ℝ)) ≤ 1700 * √(((k + 1 : ℕ) : ℝ)) := by
    linarith
  have hMUpper : (M : ℝ) ≤ 24 * (d : ℝ) := by exact_mod_cast hupper
  have hcountReal : 3 * (S : ℝ) * (rothNumberNat (M / 2) : ℝ) ≤
      4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
    exact_mod_cast hcount
  have hasiReal :
      (copies : ℝ) * (((q : ℝ) ^ omega K) ^ (9519 * k)) ≤
        (((((q + 2 : ℕ) : ℝ) ^ 30000) ^ k)) := by
    have hasi' := hasi
    rw [cwFirstPowerCubeVolume_rpow_omega_div_three K q k hq] at hasi'
    simpa only [cwFirstPowerDepth_add_one hk, Nat.cast_pow, Nat.cast_add,
      Nat.cast_ofNat, pow_mul] using hasi'
  have hcnt : 3 * ((P : ℝ) * (d : ℝ)) * (((q : ℝ) ^ omega K) ^ (9519 * k)) *
      (rothNumberNat (M / 2) : ℝ) ≤
        4 * (((((q + 2 : ℕ) : ℝ) ^ 30000) ^ k)) * ((M : ℝ) * (M : ℝ)) := by
    calc
      3 * ((P : ℝ) * (d : ℝ)) * (((q : ℝ) ^ omega K) ^ (9519 * k)) *
            (rothNumberNat (M / 2) : ℝ)
          = 3 * (S : ℝ) * (rothNumberNat (M / 2) : ℝ) *
              (((q : ℝ) ^ omega K) ^ (9519 * k)) := by rw [← hSP]; ring
      _ ≤ 4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) *
              (((q : ℝ) ^ omega K) ^ (9519 * k)) :=
        mul_le_mul_of_nonneg_right hcountReal (by positivity)
      _ = 4 * ((M : ℝ) * (M : ℝ)) *
              ((copies : ℝ) * (((q : ℝ) ^ omega K) ^ (9519 * k))) := by ring
      _ ≤ 4 * ((M : ℝ) * (M : ℝ)) * (((((q + 2 : ℕ) : ℝ) ^ 30000) ^ k)) :=
        mul_le_mul_of_nonneg_left hasiReal (by positivity)
      _ = 4 * (((((q + 2 : ℕ) : ℝ) ^ 30000) ^ k)) * ((M : ℝ) * (M : ℝ)) := by ring
  have hrate := Growth.le_mul_exp_of_mul_rothNumberNat_le (M := M)
    (a := 3 * ((P : ℝ) * (d : ℝ)) * (((q : ℝ) ^ omega K) ^ (9519 * k)))
    (b := 4 * (((((q + 2 : ℕ) : ℝ) ^ 30000) ^ k)))
    (U := 24 * (d : ℝ)) (t := 1700 * √(((k + 1 : ℕ) : ℝ)))
    (by omega) (by positivity) (by positivity) hMUpper ht hcnt
  have hremoveExp :
      (P : ℝ) * (((q : ℝ) ^ omega K) ^ (9519 * k)) ≤
        96 * Real.exp (1700 * √(((k + 1 : ℕ) : ℝ))) *
          (((((q + 2 : ℕ) : ℝ) ^ 30000) ^ k)) := by
    have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdPos
    refine le_of_mul_le_mul_right ?_ (show (0 : ℝ) < 3 * (d : ℝ) by positivity)
    calc
      (P : ℝ) * (((q : ℝ) ^ omega K) ^ (9519 * k)) * (3 * (d : ℝ))
          = 3 * ((P : ℝ) * (d : ℝ)) * (((q : ℝ) ^ omega K) ^ (9519 * k)) := by ring
      _ ≤ 3 * (4 * (((((q + 2 : ℕ) : ℝ) ^ 30000) ^ k))) * (24 * (d : ℝ)) *
            Real.exp (1700 * √(((k + 1 : ℕ) : ℝ))) := hrate
      _ = 96 * Real.exp (1700 * √(((k + 1 : ℕ) : ℝ))) *
            (((((q + 2 : ℕ) : ℝ) ^ 30000) ^ k)) * (3 * (d : ℝ)) := by ring
  have hentropy := WordType.ternaryEntropyBase_pow_le_cubic_mul_multinomial
    10481 19038 481 k (by norm_num) (by norm_num) (by norm_num) hk
  rw [← card_cwFirstPowerMarginalTypeClass hk] at hentropy
  change WordType.ternaryEntropyBase 10481 19038 481 ^ k ≤
    WordType.ternaryMultinomialLoss 10481 19038 481 k * (P : ℝ) at hentropy
  have hdeterministic :
      WordType.ternaryEntropyBase 10481 19038 481 ^ k *
          (((q : ℝ) ^ omega K) ^ (9519 * k)) ≤
        cwFirstPowerSubexponentialLoss k *
          (((((q + 2 : ℕ) : ℝ) ^ 30000) ^ k)) := by
    calc
      _ ≤ (WordType.ternaryMultinomialLoss 10481 19038 481 k * (P : ℝ)) *
          (((q : ℝ) ^ omega K) ^ (9519 * k)) := by gcongr
      _ = WordType.ternaryMultinomialLoss 10481 19038 481 k *
          ((P : ℝ) * (((q : ℝ) ^ omega K) ^ (9519 * k))) := by ring
      _ ≤ WordType.ternaryMultinomialLoss 10481 19038 481 k *
          (96 * Real.exp (1700 * √(((k + 1 : ℕ) : ℝ))) *
            (((((q + 2 : ℕ) : ℝ) ^ 30000) ^ k))) :=
        mul_le_mul_of_nonneg_left hremoveExp (by
          unfold WordType.ternaryMultinomialLoss
          positivity)
      _ = _ := by unfold cwFirstPowerSubexponentialLoss; ring
  rw [mul_pow, ← pow_mul]
  exact hdeterministic

/-- Limiting scalar inequality of the full six-constituent first-power CW construction. -/
theorem cwFirstPower_base_inequality (hq : 0 < q) :
    WordType.ternaryEntropyBase 10481 19038 481 *
        (((q : ℝ) ^ omega K) ^ 9519) ≤
      (((q + 2 : ℕ) : ℝ) ^ 30000) := by
  apply Growth.le_of_pow_succ_le_subexponential_mul_pow_succ
    (show 0 ≤ (((q + 2 : ℕ) : ℝ) ^ 30000) by positivity)
    cwFirstPowerSubexponentialLoss_subexponential
  intro n
  exact cwFirstPower_rate_inequality K q (n + 1) hq (by omega)

end FiniteAsymptoticSum

end AlgebraicComplexity.Examples
