/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRectangularType

/-!
# Rectangular-type hashing extraction for the full Coppersmith--Winograd tensor

This module is the `(a, b, e, f)`-generalization of the extraction half of
`Examples/CoppersmithWinogradFirstPowerHashing.lean`.  Where that file selects the single rational
type `(9519k, 9519k, 481k, 481k)` and extracts many independent copies of the *square* product
`⟨q^{9519k}, q^{9519k}, q^{9519k}⟩`, this one selects Huang--Pan's rectangular profile
`cwRectType a b e f` and extracts many independent copies of the *rectangular* product
`⟨q^b, q^b, q^a⟩`, which is `⟨n, n, n^r⟩` for `n = q^b` and `r = a/b`.

Only two things change relative to the square pipeline:

* the keep-block predicate is **leg-dependent** -- the three leg marginals of
  `cwRectType a b e f` differ as soon as `a ≠ b` or `e ≠ f` -- which
  `PartitionedTensor.select` and
  `PartitionHashEncoding.filter_modeledLegalTargets_eq_of_mem_iff` already support;
* the competitor list is bounded by the leg-dependent type-restricted fiber
  `cwRectLegTypedFiber` of `Examples/CoppersmithWinogradRectangularType.lean`, whose maximum over
  the three legs is `cwRectTypedFiberBound`.

## Main results

* `mem_cwRectTypeWords_iff_keepBlocks` -- the rectangular type class is exactly the conjunction of
  the three leg-local marginal conditions;
* `cwRectTypePartitionedPower_constituent_restricts_rectangular` -- every surviving constituent
  restricts to `⟨q^b, q^b, q^a⟩`;
* `exists_cwPower_rectangularExtraction_of_fieldCard` -- the finite extraction statement: a
  hashing field of size at least `12 · cwRectTypedFiberBound a b e f` and a progression-free set
  `B` produce a seed whose isolated address family is large and carries a direct sum of identical
  rectangular products.

At `(a, b, e, f) = (9519k, 9519k, 481k, 481k)` every statement here is the corresponding
statement of the square pipeline, up to the (propositional, not definitional) identification
`cwRectDepth = cwFirstPowerDepth` of `cwRectDepth_firstPower`.

## References

* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299, Sections 5 and 7.1.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-! ## Leg-local selection at the rectangular type -/

/-- Keep the leg words whose multiplicity type is the leg marginal of `cwRectType a b e f`.

Unlike the square pipeline the threshold genuinely depends on the leg: Huang--Pan's zeroing keeps
`(r(N-L)+2L, 2(N-L), rL)` on the `x` leg and `(N+rL, (1+r)(N-L), L)` on the other two. -/
noncomputable def cwRectKeepBlock (a b e f : ℕ) (c : Leg)
    (word : PositiveWord CWBlock (cwRectDepth a b e f)) : Prop :=
  WordType.multiplicity (positiveWordEquiv CWBlock (cwRectDepth a b e f) word) =
    cwRectMarginalType a b e f c

noncomputable instance cwRectKeepBlock_decidable (a b e f : ℕ) (c : Leg)
    (word : PositiveWord CWBlock (cwRectDepth a b e f)) :
    Decidable (cwRectKeepBlock a b e f c word) := by
  classical
  unfold cwRectKeepBlock
  infer_instance

/-- The rectangular joint multiplicity type is exactly the conjunction of the three leg-local
marginal conditions.  The forward direction is `cwRectLegWord_multiplicity`; the converse is
`cwRectType_unique_of_mappedTypes`. -/
theorem mem_cwRectTypeWords_iff_keepBlocks (a b e f : ℕ)
    (w : PositiveWord cwBlockSupport (cwRectDepth a b e f)) :
    w ∈ cwRectTypeWords a b e f ↔
      ∀ c, cwRectKeepBlock a b e f c
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          (cwRectDepth a b e f) w c) := by
  constructor
  · intro hw c
    exact cwRectLegWord_multiplicity a b e f (cwRectDepth a b e f) w hw c
  · intro hkeep
    rw [cwRectTypeWords, mem_positiveTypeClass]
    apply cwRectType_unique_of_mappedTypes a b e f
    intro c
    have hc := hkeep c
    unfold cwRectKeepBlock at hc
    rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)] at hc
    change WordType.multiplicity
      ((fun s : cwBlockSupport ↦ s.1 c) ∘
        positiveWordEquiv cwBlockSupport (cwRectDepth a b e f) w) = _ at hc
    rwa [WordType.multiplicity_comp_eq_mappedType] at hc

/-! ## Hashing targets and competitor counting -/

/-- Legal affine-hashing targets representing the rectangular-type CW words. -/
noncomputable def cwRectTypeTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (a b e f : ℕ) :
    Finset (ProgressionHash.LegalTriple R (Fin (cwRectDepth a b e f + 1)) 2) :=
  (cwPartitionHashEncoding (R := R)).legalTargets
    (cwRectDepth a b e f) (cwRectTypeWords a b e f)

@[simp] theorem card_cwRectTypeTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (a b e f : ℕ) :
    (cwRectTypeTargets (R := R) a b e f).card = (cwRectTypeWords a b e f).card :=
  PartitionHashEncoding.card_legalTargets _ _ _

/-- The uniform-over-legs type-restricted competitor bound.  By `cwRectLegTypedFiber_X_le_Y` it
equals the `y`-leg fiber whenever `b ≤ a`, `2e ≤ b` and `e ≤ f`, i.e. in Huang--Pan's regime. -/
def cwRectTypedFiberBound (a b e f : ℕ) : ℕ :=
  max (cwRectLegTypedFiber a b e f .X) (cwRectLegTypedFiber a b e f .Y)

theorem cwRectTypedFiberBound_pos (a b e f : ℕ) : 0 < cwRectTypedFiberBound a b e f :=
  lt_of_lt_of_le (cwRectLegTypedFiber_pos a b e f .X) (le_max_left _ _)

theorem cwRectLegTypedFiber_le_bound (a b e f : ℕ) (c : Leg) :
    cwRectLegTypedFiber a b e f c ≤ cwRectTypedFiberBound a b e f := by
  cases c
  · exact le_max_left _ _
  · exact le_max_right _ _
  · exact le_max_right _ _

/-- **Huang--Pan's "select the larger former bound".**  For `b ≤ a`, `2e ≤ b` and `e ≤ f` the
maximum is attained on the `y` and `z` legs. -/
theorem cwRectTypedFiberBound_eq_Y {a b e f : ℕ} (hba : b ≤ a) (heb : 2 * e ≤ b) (hef : e ≤ f) :
    cwRectTypedFiberBound a b e f = cwRectLegTypedFiber a b e f .Y :=
  max_eq_right (cwRectLegTypedFiber_X_le_Y hba heb hef)

/-- **The reversed selection of [HP98, Section 7.2, p. 277].**  For `a ≤ b`, `2e ≤ b` and `f ≤ e`
the maximum is attained on the `x` leg instead. -/
theorem cwRectTypedFiberBound_eq_X {a b e f : ℕ} (hab : a ≤ b) (heb : 2 * e ≤ b) (hfe : f ≤ e) :
    cwRectTypedFiberBound a b e f = cwRectLegTypedFiber a b e f .X :=
  max_eq_left (cwRectLegTypedFiber_Y_le_X hab heb hfe)

/-- Every fixed-leg fiber of rectangular-type CW hashing targets is bounded by the type-restricted
competitor count. -/
theorem card_cwRectTypeTarget_legFiber_le
    {R : Type*} [Field R] [NeZero (2 : R)] {a b e f : ℕ} (hd : 0 < a + 2 * b + 2 * e + f)
    {triple : ProgressionHash.LegalTriple R (Fin (cwRectDepth a b e f + 1)) 2}
    (htriple : triple ∈ cwRectTypeTargets (R := R) a b e f) (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber
      (cwRectTypeTargets (R := R) a b e f) triple c).card ≤ cwRectTypedFiberBound a b e f := by
  classical
  change triple ∈ (cwRectTypeWords a b e f).image
    ((cwPartitionHashEncoding (R := R)).legalTriple (cwRectDepth a b e f)) at htriple
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp htriple
  have hlegal : (cwPartitionHashEncoding (R := R)).legalTriple
      (cwRectDepth a b e f) w ∈ cwRectTypeTargets (R := R) a b e f := by
    unfold cwRectTypeTargets PartitionHashEncoding.legalTargets
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  refine ((cwPartitionHashEncoding (R := R)).card_legFiber_legalTargets_le_card_typedWordMapFiber
    (cwRectDepth a b e f) (cwRectTypeWords a b e f) (cwRectType a b e f)
    (fun word hword ↦ mem_positiveTypeClass.mp hword) hlegal c).trans ?_
  refine le_trans (le_of_eq ?_) (cwRectLegTypedFiber_le_bound a b e f c)
  refine card_cwRectTypedWordMapFiber (cwRectDepth_add_one hd) c _ ?_
  simpa using cwRectLegWord_multiplicity a b e f (cwRectDepth a b e f) w hw c

/-- The all-leg competitor list for a rectangular-type CW target has size at most
`3 · cwRectTypedFiberBound a b e f`. -/
theorem card_cwRectTypeTarget_legwiseCompetitors_le
    {R : Type*} [Field R] [NeZero (2 : R)] {a b e f : ℕ} (hd : 0 < a + 2 * b + 2 * e + f)
    {triple : ProgressionHash.LegalTriple R (Fin (cwRectDepth a b e f + 1)) 2}
    (htriple : triple ∈ cwRectTypeTargets (R := R) a b e f) :
    (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
      (cwRectTypeTargets (R := R) a b e f) triple).card ≤
        3 * cwRectTypedFiberBound a b e f := by
  apply ProgressionHash.LegalTriple.card_legwiseCompetitorYIndices_le_three_mul
  intro c
  exact card_cwRectTypeTarget_legFiber_le hd htriple c

/-- A hashing field of size at least `12 · cwRectTypedFiberBound a b e f` satisfies the
quarter-degree condition of the one-pass all-leg isolation theorem. -/
theorem cwRectType_competitorQuarter_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)] {a b e f : ℕ}
    (hd : 0 < a + 2 * b + 2 * e + f)
    (hcard : 12 * cwRectTypedFiberBound a b e f ≤ Fintype.card R) :
    ∀ triple ∈ cwRectTypeTargets (R := R) a b e f,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (cwRectTypeTargets (R := R) a b e f) triple).card ≤ Fintype.card R := by
  intro triple htriple
  calc
    4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (cwRectTypeTargets (R := R) a b e f) triple).card ≤
          4 * (3 * cwRectTypedFiberBound a b e f) :=
      Nat.mul_le_mul_left 4 (card_cwRectTypeTarget_legwiseCompetitors_le hd htriple)
    _ = 12 * cwRectTypedFiberBound a b e f := by ring
    _ ≤ Fintype.card R := hcard

/-! ## The rectangular-type tensor power -/

section TensorPower

variable (K : Type u) [CommRing K]
variable (q a b e f : ℕ)

/-- The rectangular-type subpartition of the `(a + 2b + 2e + f)`-fold CW tensor power. -/
noncomputable def cwRectTypePartitionedPower :
    PartitionedTensor (K := K)
      (A := fun _ ↦ PositiveWord CWBlock (cwRectDepth a b e f))
      (PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
        (cwRectDepth a b e f)) :=
  ((cwPartitionedTensor K q).positivePower (cwRectDepth a b e f)).select
    (cwRectKeepBlock a b e f)

/-- The selected partition support is exactly the modeled rectangular-type legal-target family. -/
theorem cwRectTypePartitionedPower_support
    {R : Type*} [Field R] [NeZero (2 : R)] :
    (cwRectTypePartitionedPower K q a b e f).support =
      (cwPartitionHashEncoding (R := R)).modeledAddresses
        (cwRectDepth a b e f) (cwRectTypeTargets (R := R) a b e f) := by
  classical
  unfold cwRectTypePartitionedPower cwRectTypeTargets
  change ((cwPartitionedTensor K q).positivePower (cwRectDepth a b e f)).support.filter
      (fun s ↦ ∀ c, cwRectKeepBlock a b e f c (s c)) = _
  rw [(cwPartitionHashEncoding (R := R)).positivePower_support_eq_modeledLegalTargets
    (cwPartitionedTensor K q) (cwRectDepth a b e f)]
  exact (cwPartitionHashEncoding (R := R)).filter_modeledLegalTargets_eq_of_mem_iff
    (cwRectDepth a b e f) (cwRectTypeWords a b e f) (cwRectKeepBlock a b e f)
      (mem_cwRectTypeWords_iff_keepBlocks a b e f)

/-- Every constituent retained by rectangular-type selection restricts to the same rectangular
matrix-multiplication tensor `⟨q^b, q^b, q^a⟩`.  For `a = r·b` this is `⟨n, n, n^r⟩` with
`n = q^b`, exactly Huang--Pan's block product [HP98, p. 276]. -/
theorem cwRectTypePartitionedPower_constituent_restricts_rectangular
    (s : (cwRectTypePartitionedPower K q a b e f).support) :
    Restricts ((cwRectTypePartitionedPower K q a b e f).constituent s.1)
      (matrixMultiplication (K := K) (q ^ b) (q ^ b) (q ^ a)) := by
  have hsSelected := (PartitionedTensor.mem_select_support
    ((cwPartitionedTensor K q).positivePower (cwRectDepth a b e f))
    (cwRectKeepBlock a b e f) s.1).mp s.2
  obtain ⟨hsPower, hsKeep⟩ := hsSelected
  obtain ⟨word, haddress⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support
      (cwRectDepth a b e f) hsPower
  change PositiveWord cwBlockSupport (cwRectDepth a b e f) at word
  change positiveSupportWordBlockAddress cwBlockSupport
    (cwRectDepth a b e f) word = s.1 at haddress
  have hsKeepWord : ∀ c, cwRectKeepBlock a b e f c
      (PartitionHashEncoding.supportWordAddress
        (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
        (cwRectDepth a b e f) word c) := by
    intro c
    unfold PartitionHashEncoding.supportWordAddress
    have hc := congrFun haddress c
    rw [hc]
    exact hsKeep c
  have hword : word ∈ cwRectTypeWords a b e f :=
    (mem_cwRectTypeWords_iff_keepBlocks a b e f word).mpr hsKeepWord
  have hwordTensor : word ∈ positiveTypeClass
      (cwPartitionedTensor K q).support (cwRectDepth a b e f)
        (cwRectType a b e f) := hword
  have hrestrict := Tensor.Restricts.positivePower_constituent_matrixMultiplication
    (cwPartitionedTensor K q)
    (cwTensorConstituentM K q) (cwTensorConstituentN K q)
    (cwTensorConstituentP K q)
    (cwSupportedConstituent_restricts K q)
    (cwRectDepth a b e f) word
  change Restricts
    (((cwPartitionedTensor K q).positivePower (cwRectDepth a b e f)).constituent
      (positiveSupportWordBlockAddress cwBlockSupport
        (cwRectDepth a b e f) word)) _ at hrestrict
  rw [haddress] at hrestrict
  have hm := cwRect_positiveWordProduct_m K q a b e f (cwRectDepth a b e f) hwordTensor
  have hn := cwRect_positiveWordProduct_n K q a b e f (cwRectDepth a b e f) hwordTensor
  have hp := cwRect_positiveWordProduct_p K q a b e f (cwRectDepth a b e f) hwordTensor
  rw [hm, hn, hp] at hrestrict
  simpa only [cwRectTypePartitionedPower, PartitionedTensor.select] using hrestrict

/-- The canonical `(a + 2b + 2e + f)`-fold tensor power restricts to the rectangular-type
partition. -/
theorem cwPower_restricts_rectTypePartitionedPower :
    Restricts
      (Tensor.power (cwPartitionedTensor K q).realize (cwRectDepth a b e f + 1))
      (cwRectTypePartitionedPower K q a b e f).realize :=
  (Tensor.Restricts.power_partitionedPositivePower
      (cwPartitionedTensor K q) (cwRectDepth a b e f)).trans
    (Tensor.Restricts.partitionedSelect
      ((cwPartitionedTensor K q).positivePower (cwRectDepth a b e f))
      (cwRectKeepBlock a b e f))

/-- For a fixed hash seed the rectangular-type CW tensor power restricts to a genuine indexed
direct sum whose addresses are isolated on all three legs. -/
theorem cwPower_restricts_rectLegwiseIsolatedIndexedDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwRectDepth a b e f + 1))) :
    Restricts
      (Tensor.power (cwPartitionedTensor K q).realize (cwRectDepth a b e f + 1))
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
            (cwRectDepth a b e f))
          ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed))
        (fun s : (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed ↦
          (cwRectTypePartitionedPower K q a b e f).constituent s.1)) := by
  apply (cwPower_restricts_rectTypePartitionedPower K q a b e f).trans
  apply Tensor.Restricts.modeledTargets_to_legwiseIsolatedIndexedDirectSum
    (cwPartitionHashEncoding (R := R)) (cwRectTypeWords a b e f) B hB seed
      (cwRectTypePartitionedPower K q a b e f)
  exact cwRectTypePartitionedPower_support K q a b e f

/-- The legwise-isolated constituent sum restricts componentwise to identical rectangular
matrix-multiplication tensors. -/
theorem cwRectLegwiseIsolatedIndexedDirectSum_restricts_rectangularDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (cwRectDepth a b e f + 1))) :
    Restricts
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
            (cwRectDepth a b e f))
          ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed))
        (fun s : (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed ↦
          (cwRectTypePartitionedPower K q a b e f).constituent s.1))
      (matrixMultiplicationDirectSum
        (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
          (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed)
        K (fun _ ↦ q ^ b) (fun _ ↦ q ^ b) (fun _ ↦ q ^ a)) := by
  apply Tensor.Restricts.indexedDirectSum
  intro s
  have hsModeled : s.1 ∈
      (cwPartitionHashEncoding (R := R)).modeledAddresses
        (cwRectDepth a b e f) (cwRectTypeTargets (R := R) a b e f) := by
    apply (cwPartitionHashEncoding (R := R)).filteredPowerAddresses_subset_modeledAddresses
      (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed
    apply
      (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses_subset_filteredPowerAddresses
      (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed
    exact s.2
  let selected : (cwRectTypePartitionedPower K q a b e f).support :=
    ⟨s.1, by
      rw [cwRectTypePartitionedPower_support (R := R) K q a b e f]
      exact hsModeled⟩
  simpa only [selected] using
    cwRectTypePartitionedPower_constituent_restricts_rectangular K q a b e f selected

/-- A fixed successful hash seed extracts independent copies of `⟨q^b, q^b, q^a⟩` from the
canonical `(a + 2b + 2e + f)`-fold CW tensor power. -/
theorem cwPower_restricts_rectLegwiseIsolatedRectangularDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwRectDepth a b e f + 1))) :
    Restricts
      (Tensor.power (cwPartitionedTensor K q).realize (cwRectDepth a b e f + 1))
      (matrixMultiplicationDirectSum
        (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
          (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed)
        K (fun _ ↦ q ^ b) (fun _ ↦ q ^ b) (fun _ ↦ q ^ a)) :=
  (cwPower_restricts_rectLegwiseIsolatedIndexedDirectSum K q a b e f B hB seed).trans
    (cwRectLegwiseIsolatedIndexedDirectSum_restricts_rectangularDirectSum K q a b e f B seed)

/-- Finite rectangular-type extraction with the exact division-free hashing count. -/
theorem exists_cwPower_rectangularExtraction
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ cwRectTypeTargets (R := R) a b e f,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (cwRectTypeTargets (R := R) a b e f) triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (cwRectDepth a b e f + 1)),
      3 * (cwRectTypeWords a b e f).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed).card ∧
        Restricts
          (Tensor.power (cwPartitionedTensor K q).realize (cwRectDepth a b e f + 1))
          (matrixMultiplicationDirectSum
            (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed)
            K (fun _ ↦ q ^ b) (fun _ ↦ q ^ b) (fun _ ↦ q ^ a)) := by
  obtain ⟨seed, hcount, _hsubset, _hinjective⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_legwiseIsolatedTargets
      (cwRectTypeTargets (R := R) a b e f) B hB hquarter
  refine ⟨seed, ?_,
    cwPower_restricts_rectLegwiseIsolatedRectangularDirectSum K q a b e f B hB seed⟩
  rw [(cwPartitionHashEncoding (R := R)).card_legwiseIsolatedPowerAddresses
    (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed]
  change 3 * ((cwPartitionHashEncoding (R := R)).legalTargets
      (cwRectDepth a b e f) (cwRectTypeWords a b e f)).card * B.card ≤ _ at hcount
  rw [PartitionHashEncoding.card_legalTargets] at hcount
  exact hcount

/-- Finite rectangular-type extraction with competitor counting internalized: only the explicit
field-size and progression-free-set inputs remain.  The field-size threshold is Huang--Pan's
`M ≍ 2·(competitor count)` of [HP98, p. 276]. -/
theorem exists_cwPower_rectangularExtraction_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (hd : 0 < a + 2 * b + 2 * e + f)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hcard : 12 * cwRectTypedFiberBound a b e f ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (cwRectDepth a b e f + 1)),
      3 * (cwRectTypeWords a b e f).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed).card ∧
        Restricts
          (Tensor.power (cwPartitionedTensor K q).realize (cwRectDepth a b e f + 1))
          (matrixMultiplicationDirectSum
            (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwRectDepth a b e f) (cwRectTypeWords a b e f) B seed)
            K (fun _ ↦ q ^ b) (fun _ ↦ q ^ b) (fun _ ↦ q ^ a)) :=
  exists_cwPower_rectangularExtraction K q a b e f B hB
    (cwRectType_competitorQuarter_of_fieldCard hd hcard)

end TensorPower

end AlgebraicComplexity.Examples
