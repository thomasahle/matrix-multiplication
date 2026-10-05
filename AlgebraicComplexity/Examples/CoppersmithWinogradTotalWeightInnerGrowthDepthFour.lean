import AlgebraicComplexity.Analysis.LogConstants
import AlgebraicComplexity.Analysis.MaximumEntropyTypeCountingGrowth
import AlgebraicComplexity.Examples.CoppersmithWinogradChunkTypedLeaf
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerSequenceDepth
import AlgebraicComplexity.Probability.KullbackLeiblerBasic

/-!
# A concrete depth-four inner growth datum and its localized-ambient bound

`CWTotalWeightInnerGrowthDataAtDepth` (see
`Examples/CoppersmithWinogradTotalWeightInnerSequenceDepth.lean`) packages the *one genuinely
quantitative* input of the total-weight inner extraction: an exact proportional coarse-word
sequence together with the localized-ambient cardinality bound

`(cwTotalWeightLocalizedAmbientWords …).card ≤ ambientLoss k * ambientBase ^ k`.

Until now that structure had no producer at any depth.  This module supplies one, depth-generically
and then concretely at the certificate's parameters `q = 5`, `depth = 4`.

## What the ambient bound really is

`cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord` is the set of fine chunk words
of length `n + 1` that (i) coarsen to the fixed quotient word `coarseWord` and (ii) have the three
prescribed fine leg marginal types.  Dropping (i) — which only shrinks the family, by
`cwTotalWeightLocalizedAmbientWords_subset_fineMarginalAmbientWords` — leaves exactly a
*three-marginal fiber*, and that is the object the method-of-types layer already bounds:

`WordType.card_words_le_typeCount_mul_structuralZeroLoss_mul_referenceTypeClass`

says that any word family all of whose members share the three mapped types of a reference profile
is at most a polynomial factor larger than the reference type class, **provided** the normalized
reference law maximizes entropy in its mapped fiber.  Composing that with
`WordType.multinomial_le_upperLoss_mul_proportionalEntropyBase_pow` turns the type class into the
clean exponential `proportionalEntropyBase reference ^ k`.

So the ambient bound is not an extra unproved estimate: it is *exactly* the conditional
maximum-entropy hypothesis

`WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K q depth) (normalized reference)`

plus already-committed analysis.  That is the content of
`card_cwTotalWeightLocalizedAmbientWords_le` and of the constructor
`cwChunkInnerGrowthDataOfMaximumEntropy`.

## Discharging the maximum-entropy hypothesis

`isMaximumEntropyInMappedFiber_of_logLinear` is the finite Gibbs criterion: a strictly positive law
whose log-density splits as a constant plus one potential per visible coordinate is automatically
the entropy maximizer of its mapped fiber.  It is the coordinate-family generalization of the
argument already carried out by hand for the CW square in
`Examples/CoppersmithWinogradSquareEntropy.lean`, and it belongs in
`Analysis/MaximumEntropyMappedFiber.lean` once this tranche lands.

`isMaximumEntropyInMappedFiber_const` is its degenerate case (all potentials zero), which discharges
the hypothesis unconditionally for a *constant* profile.  That is what makes
`cwChunkConstantInnerGrowthDataLevelFour` an axiom-free, hypothesis-free depth-four datum.

The constant profile is deliberately not claimed to be the laser-optimal one: it clears the volume
floor with room to spare (see below) but says nothing about `hWrate`.  A rate-clearing profile is a
*product* profile over the `2 ^ depth` chunk letters, and for such a profile the log-density is
again log-linear in the three chunk leg words, so `isMaximumEntropyInMappedFiber_of_logLinear`
applies verbatim; only the arithmetic of the potentials changes: one solves
`w(b) = A_{b .X} · B_{b .Y} · C_{b .Z}` over the six supported CW blocks and takes
`potential c word = ∑_j log (of the corresponding factor at position j)`.

## The volume floor

Two volume floors are in play.  `MatrixMultiplication/TotalWeightAcceptanceFloors.lean` fixes the
`C′` floor `volumeFloor = 15021/2500 = 6.0084` at `strideValue = 38`, while the level-four endpoint
adapter still consumes the older `3755689/625000 = 6.0091024` of
`Generated/TotalQuotientVolumeScalarData.lean`.  The obligation is
`2 ^ (3 * 38 * v) ≤ dimX * dimY * dimZ`.

For a `CW_5` leaf the dimension product is `5 ^ m`, where `m` is the total one-type letter count of
the profile (a base block contributes a factor `q` exactly when it is one of `cw011`, `cw101`,
`cw110`).  The integrality analysis of `TotalWeightAcceptanceFloors` asks for
`m ≥ ⌈3 * 38 * v / log₂ 5⌉`, i.e. `m ≥ 295` at the `C′` floor (mean volume `6.00849814`) and
`m ≥ 296` at the older one.

The constant-`19` depth-four leaf built here reaches `m ≥ 19 * 16 = 304` — that much already from
the single all-`cw011` chunk letter, since every other letter has volume at least `1` — so it
clears both floors with mean volume `6.19181` rather than the minimal `6.00850`.
`two_rpow_le_five_pow_304`, `cwChunkConstantLeafLevelFour_volumeFloor` and
`cwChunkConstantLeafLevelFour_acceptanceVolumeFloor` prove this: exact `Nat` arithmetic for the
product, the certified `log 2` / `log 5` enclosures of `Analysis/LogConstants.lean` for the
base-two comparison.

## The level-four index convention, and the alignment blocker

The depth-four outer datum of `Examples/CoppersmithWinogradTotalWeightOuterDepthFour.lean` has
`n r = 19 * r - 1`, forced by the chunk alignment `8 * 38 * r = 16 * (19 * r)`, and
`omega_lt_236999_of_levelFourCanonicalInner` requires `hn : ∀ r, outer.n r = growth.exponent r`.
Both growth-datum constructors here have `exponent k = profileMass reference * k - 1`, so they meet
that convention **exactly when `profileMass reference = 19`**;
`cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe_exponent_levelFour` records this.

That is why the zero-safe constructor exists.  `PositiveIntegralProfile.count_pos` demands a
strictly positive count on **every** letter of `(cwChunkPartitionedTensor K 5 4).support`, and that
alphabet has `6 ^ 16 ≈ 2.8 · 10 ^ 12` letters, so **every** rational typed leaf over the full
depth-four chunk support has `profileMass ≥ 6 ^ 16`, never `19`.  The unconditional instance below,
`cwChunkConstantInnerGrowthDataLevelFour`, therefore has `exponent r = 19 * 6 ^ 16 * r - 1` and does
*not* satisfy `hn` against the S6 outer datum: it is an existence witness for the ambient bound, not
a component of the assembly.

The resolution is the sparse/embedded leaf route (`EmbeddedRationalTypedLeaf*`,
`CoppersmithWinogradTotalWeightEmbeddedInner*`): let the leaf live on its own small alphabet and
embed into the large partition support.  Everything in this file is written so that it survives that
change — `cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe` needs only `0 < profileMass reference` and
the maximum-entropy property, and `cwChunkLevelFour_volumeFloor_of_oneTypeCount` needs only that the
profile puts multiplicity `19` on the all-`cw011` chunk letter, which a mass-`19` profile
concentrated there does.

What is *not* supplied here is the maximum-entropy certificate for such a sparse profile.
`isMaximumEntropyInMappedFiber_of_logLinear` requires strict positivity of the law on the whole
alphabet, so it does not apply to a sparse reference; a sparse profile needs either marginal
rigidity (`RationalTypedLeaf.IsMarginalRigid.isMaximumEntropyBits`) or a maximum-entropy predicate
relativized to the embedded alphabet.  That is the one genuinely open input on the inner side.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u v w

variable {I : Type u} [Fintype I]
variable {C : Type v} [Fintype C]
variable {A : C → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Expectation of a finite sum of statistics is the sum of the expectations. -/
theorem expectation_finset_sum (p : ProbabilityVector I) (f : C → I → ℝ) :
    p.expectation (fun i ↦ ∑ c, f c i) = ∑ c, p.expectation (f c) := by
  unfold ProbabilityVector.expectation
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- **Finite Gibbs criterion.**  A strictly positive law whose log-density is a constant plus one
potential per visible coordinate maximizes entropy among all laws with the same visible
pushforwards.

This is the coordinate-family form of the argument carried out by hand for the CW-square joint law
in `Examples/CoppersmithWinogradSquareEntropy.lean`.  Proof: the log-linear identity makes the
expected reference log-density a function of the pushforwards alone, so a competitor in the same
mapped fiber has the same expectation; Gibbs' inequality then turns the entropy gap into a
nonnegative Kullback--Leibler divergence. -/
theorem isMaximumEntropyInMappedFiber_of_logLinear
    (coordinate : ∀ c, I → A c) (p : ProbabilityVector I)
    (hp : ∀ i, 0 < p.weight i)
    (kappa : ℝ) (potential : ∀ c, A c → ℝ)
    (hlog : ∀ i, Real.log (p.weight i) =
      kappa + ∑ c, potential c (coordinate c i)) :
    IsMaximumEntropyInMappedFiber coordinate p := by
  intro q hq
  have hcoordinate : ∀ c : C,
      q.expectation (fun i ↦ potential c (coordinate c i)) =
        p.expectation (fun i ↦ potential c (coordinate c i)) := by
    intro c
    exact ProbabilityVector.expectation_comp_eq_of_pushforward_eq
      (coordinate c) q p (hq c) (potential c)
  have hsum : ∀ r : ProbabilityVector I,
      r.expectation (fun i ↦ Real.log (p.weight i)) =
        kappa + ∑ c, r.expectation (fun i ↦ potential c (coordinate c i)) := by
    intro r
    calc
      r.expectation (fun i ↦ Real.log (p.weight i)) =
          r.expectation (fun i ↦ kappa + ∑ c, potential c (coordinate c i)) :=
        r.expectation_congr hlog
      _ = r.expectation (fun _ ↦ kappa) +
            r.expectation (fun i ↦ ∑ c, potential c (coordinate c i)) :=
        ProbabilityVector.expectation_add r (fun _ ↦ kappa) _
      _ = kappa + ∑ c, r.expectation (fun i ↦ potential c (coordinate c i)) := by
        rw [ProbabilityVector.expectation_const,
          expectation_finset_sum r (fun c i ↦ potential c (coordinate c i))]
  have hlogExpectation :
      q.expectation (fun i ↦ Real.log (p.weight i)) =
        p.expectation (fun i ↦ Real.log (p.weight i)) := by
    rw [hsum q, hsum p]
    exact congrArg (kappa + ·) (Finset.sum_congr rfl fun c _ ↦ hcoordinate c)
  have hgap := ProbabilityVector.klDiv_eq_entropy_sub_of_expectation_log_eq
    q p hp hlogExpectation
  have hnonneg := ProbabilityVector.klDiv_nonneg q p hp
  linarith

/-- A constant integral profile normalizes to the uniform law, whose log-density is constant;
by `isMaximumEntropyInMappedFiber_of_logLinear` it therefore maximizes entropy in **every** mapped
fiber, with no structural input at all. -/
theorem isMaximumEntropyInMappedFiber_const
    (coordinate : ∀ c, I → A c) (m : ℕ) (hm : 0 < m)
    (hmass : 0 < profileMass (fun _ : I ↦ m)) :
    IsMaximumEntropyInMappedFiber coordinate
      (normalizedProfileProbability (fun _ : I ↦ m) hmass) := by
  have hmassReal : (0 : ℝ) < (profileMass (fun _ : I ↦ m) : ℝ) := by exact_mod_cast hmass
  have hmReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine isMaximumEntropyInMappedFiber_of_logLinear coordinate _ ?_
    (Real.log ((m : ℝ) / (profileMass (fun _ : I ↦ m) : ℝ))) (fun _ _ ↦ 0) ?_
  · intro i
    rw [normalizedProfileProbability_weight]
    exact div_pos hmReal hmassReal
  · intro i
    rw [normalizedProfileProbability_weight]
    simp

end AlgebraicComplexity.WordType

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-! ## The three visible coordinates of a chunk letter -/

/-- The three visible coordinates of a supported chunk letter are its three leg words.  This is
literally the map that `cwTotalWeightFineMarginalType` pushes a joint profile along. -/
abbrev cwChunkCoordinate (K : Type u) [CommRing K] (q depth : ℕ) (c : Leg)
    (s : (cwChunkPartitionedTensor K q depth).support) :
    PositiveWord CWBlock (2 ^ depth - 1) :=
  s.1 c

theorem cwTotalWeightFineMarginalType_eq_mappedType
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ) (c : Leg) :
    cwTotalWeightFineMarginalType K q depth profile c =
      WordType.mappedType (cwChunkCoordinate K q depth c) profile :=
  rfl

/-- A strictly positive profile on the chunk support has strictly positive mass, because the
support is nonempty. -/
theorem cwChunk_profileMass_pos
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hpos : ∀ i, 0 < reference i) :
    0 < WordType.profileMass reference := by
  classical
  have hwitness : (cwChunkSupportWitness K q depth) ∈
      (Finset.univ : Finset (cwChunkPartitionedTensor K q depth).support) :=
    Finset.mem_univ _
  exact lt_of_lt_of_le (hpos (cwChunkSupportWitness K q depth))
    (Finset.single_le_sum (f := reference) (fun j _ ↦ Nat.zero_le _) hwitness)

/-! ## Function-word transport of one localized ambient family -/

/-- Function-word presentation of one localized total-weight ambient family.

The tensor layer uses recursively parenthesized positive words; the reusable method-of-types layer
uses functions on `Fin (n + 1)`.  This is only the canonical finite-set transport between them. -/
noncomputable def cwTotalWeightLocalizedAmbientFunctionWords
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    Finset (Fin (n + 1) → (cwChunkPartitionedTensor K q depth).support) :=
  (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord).map
    (positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n).toEmbedding

@[simp] theorem card_cwTotalWeightLocalizedAmbientFunctionWords
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    (cwTotalWeightLocalizedAmbientFunctionWords K q depth n profile coarseWord).card =
      (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord).card := by
  simp [cwTotalWeightLocalizedAmbientFunctionWords]

/-- Every localized ambient function word has exactly the three mapped types of the prescribed
joint profile.  This is the hypothesis shape consumed by the maximum-entropy counting layer. -/
theorem cwTotalWeightLocalizedAmbientFunctionWord_mappedType
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (word : Fin (n + 1) → (cwChunkPartitionedTensor K q depth).support)
    (hword : word ∈
      cwTotalWeightLocalizedAmbientFunctionWords K q depth n profile coarseWord)
    (c : Leg) :
    WordType.mappedType (cwChunkCoordinate K q depth c) (WordType.multiplicity word) =
      WordType.mappedType (cwChunkCoordinate K q depth c) profile := by
  classical
  rw [cwTotalWeightLocalizedAmbientFunctionWords, Finset.mem_map] at hword
  obtain ⟨source, hsource, rfl⟩ := hword
  have hmarginal :=
    ((mem_cwTotalWeightLocalizedAmbientWords_iff K q depth n profile coarseWord source).mp
      hsource).2 c
  rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
    (A := fun _c : Leg ↦ PositiveWord CWBlock (2 ^ depth - 1))
    (support := (cwChunkPartitionedTensor K q depth).support)] at hmarginal
  change WordType.multiplicity
      (cwChunkCoordinate K q depth c ∘
        positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n source) =
    cwTotalWeightFineMarginalType K q depth profile c at hmarginal
  rw [WordType.multiplicity_comp_eq_mappedType,
    cwTotalWeightFineMarginalType_eq_mappedType] at hmarginal
  exact hmarginal

/-! ## The localized-ambient upper bound -/

/-- **The ambient bound, conditional only on maximum entropy.**

Every localized total-weight ambient family at the proportional profile `k ⋅ reference` is at most
an explicit polynomial factor larger than the reference type class, provided the normalized
reference law maximizes entropy in its three-leg mapped fiber.  Fixing the coarse word only shrinks
the family, so no permutation stability after localization is needed. -/
theorem card_cwTotalWeightLocalizedAmbientWords_le_typeClass
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hrefMass : 0 < WordType.profileMass reference)
    (hmaximum : WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K q depth)
      (WordType.normalizedProfileProbability reference hrefMass))
    (n k : ℕ) (hk : 0 < k) (hn : n + 1 = WordType.profileMass reference * k)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    ((cwTotalWeightLocalizedAmbientWords K q depth n
        (WordType.proportionalCounts reference k) coarseWord).card : ℝ) ≤
      WordType.maximumEntropyMappedFiberLoss reference k *
        (Nat.multinomial Finset.univ (WordType.proportionalCounts reference k) : ℝ) := by
  classical
  have hfinite :=
    WordType.card_words_le_typeCount_mul_structuralZeroLoss_mul_referenceTypeClass
      (cwChunkCoordinate K q depth) reference hrefMass hmaximum hk hn
      (cwTotalWeightLocalizedAmbientFunctionWords K q depth n
        (WordType.proportionalCounts reference k) coarseWord)
      (fun word hword c ↦ by
        have h := cwTotalWeightLocalizedAmbientFunctionWord_mappedType
          K q depth n (WordType.proportionalCounts reference k) coarseWord word hword c
        exact h)
  rw [card_cwTotalWeightLocalizedAmbientFunctionWords, hn] at hfinite
  refine hfinite.trans ?_
  exact mul_le_mul_of_nonneg_right
    (WordType.typeCount_mul_structuralZeroLoss_le_maximumEntropyMappedFiberLoss reference k)
    (Nat.cast_nonneg _)

/-- Explicit subexponential loss of the localized-ambient bound: the maximum-entropy fiber loss
followed by the upper method-of-types estimate.

The `+ 1` is a convenience only: `proportionalMultinomialUpperLoss` vanishes at `k = 0`, while the
growth-datum contract asks for a loss that is positive at *every* repetition. -/
noncomputable def cwChunkAmbientLoss
    {K : Type u} [CommRing K] {q depth : ℕ}
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ) (k : ℕ) : ℝ :=
  WordType.maximumEntropyMappedFiberLoss reference k *
    (WordType.proportionalMultinomialUpperLoss reference k + 1)

theorem cwChunkAmbientLoss_pos
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ) (k : ℕ) :
    0 < cwChunkAmbientLoss reference k := by
  refine mul_pos (WordType.maximumEntropyMappedFiberLoss_pos reference k) ?_
  have hupper : (0 : ℝ) ≤ WordType.proportionalMultinomialUpperLoss reference k := by
    unfold WordType.proportionalMultinomialUpperLoss
    positivity
  linarith

theorem cwChunkAmbientLoss_subexponential
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ) :
    Growth.Subexponential (cwChunkAmbientLoss reference) := by
  have hone : Growth.Subexponential (fun _ : ℕ ↦ (1 : ℝ)) := by
    simpa using Growth.Subexponential.natCast_pow 0
  exact (WordType.maximumEntropyMappedFiberLoss_subexponential reference).mul
    ((WordType.proportionalMultinomialUpperLoss_subexponential reference).add hone)

/-- The exponential form of the ambient bound: the localized ambient family grows at most at the
reference profile's own entropy base. -/
theorem card_cwTotalWeightLocalizedAmbientWords_le
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hpos : ∀ i, 0 < reference i)
    (hrefMass : 0 < WordType.profileMass reference)
    (hmaximum : WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K q depth)
      (WordType.normalizedProfileProbability reference hrefMass))
    (n k : ℕ) (hk : 0 < k) (hn : n + 1 = WordType.profileMass reference * k)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    ((cwTotalWeightLocalizedAmbientWords K q depth n
        (WordType.proportionalCounts reference k) coarseWord).card : ℝ) ≤
      cwChunkAmbientLoss reference k *
        WordType.proportionalEntropyBase reference ^ k := by
  haveI : Nonempty (cwChunkPartitionedTensor K q depth).support :=
    ⟨cwChunkSupportWitness K q depth⟩
  have hbase := WordType.multinomial_le_upperLoss_mul_proportionalEntropyBase_pow
    reference k hpos hk
  calc
    ((cwTotalWeightLocalizedAmbientWords K q depth n
        (WordType.proportionalCounts reference k) coarseWord).card : ℝ) ≤
        WordType.maximumEntropyMappedFiberLoss reference k *
          (Nat.multinomial Finset.univ (WordType.proportionalCounts reference k) : ℝ) :=
      card_cwTotalWeightLocalizedAmbientWords_le_typeClass
        K q depth reference hrefMass hmaximum n k hk hn coarseWord
    _ ≤ WordType.maximumEntropyMappedFiberLoss reference k *
        (WordType.proportionalMultinomialUpperLoss reference k *
          WordType.proportionalEntropyBase reference ^ k) :=
      mul_le_mul_of_nonneg_left hbase
        (WordType.maximumEntropyMappedFiberLoss_pos reference k).le
    _ ≤ WordType.maximumEntropyMappedFiberLoss reference k *
        ((WordType.proportionalMultinomialUpperLoss reference k + 1) *
          WordType.proportionalEntropyBase reference ^ k) := by
      have hbaseNonneg : (0 : ℝ) ≤ WordType.proportionalEntropyBase reference ^ k :=
        pow_nonneg (WordType.proportionalEntropyBase_pos_zeroSafe reference).le k
      have hstep : WordType.proportionalMultinomialUpperLoss reference k *
          WordType.proportionalEntropyBase reference ^ k ≤
            (WordType.proportionalMultinomialUpperLoss reference k + 1) *
              WordType.proportionalEntropyBase reference ^ k := by
        nlinarith
      exact mul_le_mul_of_nonneg_left hstep
        (WordType.maximumEntropyMappedFiberLoss_pos reference k).le
    _ = cwChunkAmbientLoss reference k *
        WordType.proportionalEntropyBase reference ^ k := by
      unfold cwChunkAmbientLoss
      ring

/-! ## The depth-generic growth-data constructor -/

/-- The quotient image of the canonical supported chunk letter.  Only used as a total default. -/
noncomputable def cwTotalWeightCoarseWitness
    (K : Type u) [CommRing K] (q depth : ℕ) :
    CWTotalWeightCoarseSupport K q depth :=
  (cwChunkPartitionedTensor K q depth).coarseningSupportMap
    (cwTotalWeightChunkCoarsening depth) (cwChunkSupportWitness K q depth)

/-- A canonical coarse representative of the exact proportional quotient type.

For `0 < k` the corresponding positive type class is nonempty — its cardinality is the multinomial
coefficient of a genuine type — and the definition picks an element of it.  The `k = 0` branch is a
harmless constant default; the growth-datum contract never inspects it. -/
noncomputable def cwChunkCanonicalCoarseWord
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ) (k : ℕ) :
    PositiveWord (CWTotalWeightCoarseSupport K q depth)
      (WordType.profileMass reference * k - 1) := by
  classical
  exact
    if h : (positiveTypeClass (CWTotalWeightCoarseSupport K q depth)
        (WordType.profileMass reference * k - 1)
        (WordType.proportionalCounts
          (cwTotalWeightCoarseProfile K q depth reference) k)).Nonempty then
      h.choose
    else
      positiveWordConst (cwTotalWeightCoarseWitness K q depth)
        (WordType.profileMass reference * k - 1)

/-- The canonical coarse representative really has the exact proportional quotient type. -/
theorem cwChunkCanonicalCoarseWord_multiplicity
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hrefMass : 0 < WordType.profileMass reference) (k : ℕ) (hk : 0 < k) :
    WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth)
          (WordType.profileMass reference * k - 1)
          (cwChunkCanonicalCoarseWord K q depth reference k)) =
      WordType.proportionalCounts (cwTotalWeightCoarseProfile K q depth reference) k := by
  classical
  have hlen : WordType.profileMass reference * k - 1 + 1 =
      WordType.profileMass reference * k := by
    have : 0 < WordType.profileMass reference * k := Nat.mul_pos hrefMass hk
    omega
  have htype : WordType.proportionalCounts
      (cwTotalWeightCoarseProfile K q depth reference) k ∈
      WordType.types (CWTotalWeightCoarseSupport K q depth)
        (WordType.profileMass reference * k - 1 + 1) := by
    rw [hlen, ← cwTotalWeightCoarseProfile_mass K q depth reference]
    exact WordType.proportionalCounts_mem_types _ k
  have hcard := Tensor.card_positiveTypeClass_eq_multinomial
    (I := CWTotalWeightCoarseSupport K q depth)
    (WordType.profileMass reference * k - 1)
    (WordType.proportionalCounts (cwTotalWeightCoarseProfile K q depth reference) k) htype
  have hnonempty : (positiveTypeClass (CWTotalWeightCoarseSupport K q depth)
      (WordType.profileMass reference * k - 1)
      (WordType.proportionalCounts
        (cwTotalWeightCoarseProfile K q depth reference) k)).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact Nat.multinomial_pos _ _
  have hchoice := hnonempty.choose_spec
  rw [cwChunkCanonicalCoarseWord, dif_pos hnonempty]
  exact mem_positiveTypeClass.mp hchoice

/-- **The depth-generic inner growth datum.**

Every strictly positive chunk profile whose normalized law maximizes entropy in its three-leg
mapped fiber carries a complete `CWTotalWeightInnerGrowthDataAtDepth`, with the profile's own
`proportionalEntropyBase` as ambient base.  All four structural fields are exact; the single
quantitative field `ambient_upper` is `card_cwTotalWeightLocalizedAmbientWords_le`. -/
noncomputable def cwChunkInnerGrowthDataOfMaximumEntropy
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hpos : ∀ i, 0 < reference i)
    (hmaximum : WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K q depth)
      (WordType.normalizedProfileProbability reference
        (cwChunk_profileMass_pos K q depth reference hpos))) :
    CWTotalWeightInnerGrowthDataAtDepth K q depth reference
      (WordType.proportionalEntropyBase reference)
      (cwChunkAmbientLoss reference) where
  exponent k := WordType.profileMass reference * k - 1
  coarseWord k := cwChunkCanonicalCoarseWord K q depth reference k
  length_eq k hk := by
    have hmass := cwChunk_profileMass_pos K q depth reference hpos
    have : 0 < WordType.profileMass reference * k := Nat.mul_pos hmass hk
    omega
  coarse_type k hk :=
    cwChunkCanonicalCoarseWord_multiplicity K q depth reference
      (cwChunk_profileMass_pos K q depth reference hpos) k hk
  ambientBase_nonneg := (WordType.proportionalEntropyBase_pos_zeroSafe reference).le
  ambientLoss_pos k := cwChunkAmbientLoss_pos K q depth reference k
  ambientLoss_subexponential := cwChunkAmbientLoss_subexponential K q depth reference
  ambient_upper k hk := by
    have hmass := cwChunk_profileMass_pos K q depth reference hpos
    refine card_cwTotalWeightLocalizedAmbientWords_le K q depth reference hpos hmass
      hmaximum _ k hk ?_ _
    have : 0 < WordType.profileMass reference * k := Nat.mul_pos hmass hk
    omega

/-! ## A zero-safe form: arbitrary, possibly sparse, chunk profiles

`multinomial_le_upperLoss_mul_proportionalEntropyBase_pow` needs a strictly positive profile, so
the bound above is unavailable for a profile with structural zeros.  The maximum-entropy counting
layer itself has no such restriction: `card_words_le_typeCount_mul_exp_referenceEntropy` already
delivers the exponential `exp (k * mass * H)` directly.  This section repackages that form, which is
the one the depth-four assembly actually needs — the chunk-alignment equation forces
`profileMass = 19`, far below the `6 ^ 16` letters of the depth-four chunk support, so the relevant
reference profiles are necessarily sparse.
-/

/-- Exponential ambient base of an arbitrary chunk profile: `exp (mass * H)`, where `H` is the
Shannon entropy in nats of the normalized profile.  For a strictly positive profile this is
`WordType.proportionalEntropyBase` (`proportionalEntropyBase_eq_exp_profileEntropy`). -/
noncomputable def cwChunkAmbientEntropyBase
    {K : Type u} [CommRing K] {q depth : ℕ}
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ) : ℝ :=
  Real.exp ((WordType.profileMass reference : ℝ) * WordType.profileEntropyNats reference)

theorem cwChunkAmbientEntropyBase_pos
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ) :
    0 < cwChunkAmbientEntropyBase reference :=
  Real.exp_pos _

/-- For a strictly positive profile the zero-safe base is the proportional entropy base. -/
theorem cwChunkAmbientEntropyBase_eq_proportionalEntropyBase
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hrefMass : 0 < WordType.profileMass reference) :
    cwChunkAmbientEntropyBase reference =
      WordType.proportionalEntropyBase reference :=
  (WordType.proportionalEntropyBase_eq_exp_profileEntropy reference hrefMass).symm

/-- Polynomial type-selection loss: the number of empirical types of a word of length
`profileMass reference * k`. -/
noncomputable def cwChunkAmbientTypeLoss
    {K : Type u} [CommRing K] {q depth : ℕ}
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ) (k : ℕ) : ℝ :=
  ((((WordType.profileMass reference * k + 1) ^
    Fintype.card (cwChunkPartitionedTensor K q depth).support : ℕ) : ℝ))

theorem cwChunkAmbientTypeLoss_pos
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ) (k : ℕ) :
    0 < cwChunkAmbientTypeLoss reference k := by
  unfold cwChunkAmbientTypeLoss
  exact_mod_cast pow_pos (Nat.succ_pos _) _

theorem cwChunkAmbientTypeLoss_subexponential
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ) :
    Growth.Subexponential (cwChunkAmbientTypeLoss reference) := by
  set a := WordType.profileMass reference with ha
  set d := Fintype.card (cwChunkPartitionedTensor K q depth).support with hd
  have hmajor := (Growth.Subexponential.natCast_succ_pow d).const_mul
    (show (0 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) ^ d by positivity)
  refine hmajor.mono (fun k ↦ by unfold cwChunkAmbientTypeLoss; positivity) (fun k ↦ ?_)
  have hbase : a * k + 1 ≤ (a + 1) * (k + 1) := by nlinarith
  calc
    cwChunkAmbientTypeLoss reference k ≤ ((((a + 1) * (k + 1)) ^ d : ℕ) : ℝ) := by
      unfold cwChunkAmbientTypeLoss
      exact_mod_cast Nat.pow_le_pow_left hbase d
    _ = ((a + 1 : ℕ) : ℝ) ^ d * (((k + 1 : ℕ) : ℝ)) ^ d := by
      push_cast
      rw [mul_pow]

/-- **The zero-safe ambient bound.**  No positivity hypothesis on the profile: only positive mass
and the maximum-entropy property of its normalization. -/
theorem card_cwTotalWeightLocalizedAmbientWords_le_entropyBase
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hrefMass : 0 < WordType.profileMass reference)
    (hmaximum : WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K q depth)
      (WordType.normalizedProfileProbability reference hrefMass))
    (n k : ℕ) (hk : 0 < k) (hn : n + 1 = WordType.profileMass reference * k)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    ((cwTotalWeightLocalizedAmbientWords K q depth n
        (WordType.proportionalCounts reference k) coarseWord).card : ℝ) ≤
      cwChunkAmbientTypeLoss reference k * cwChunkAmbientEntropyBase reference ^ k := by
  classical
  have hfinite :=
    WordType.card_words_le_typeCount_mul_exp_referenceEntropy
      (cwChunkCoordinate K q depth) reference hrefMass hmaximum hk hn
      (cwTotalWeightLocalizedAmbientFunctionWords K q depth n
        (WordType.proportionalCounts reference k) coarseWord)
      (fun word hword c ↦
        cwTotalWeightLocalizedAmbientFunctionWord_mappedType
          K q depth n (WordType.proportionalCounts reference k) coarseWord word hword c)
  rw [card_cwTotalWeightLocalizedAmbientFunctionWords, hn] at hfinite
  refine hfinite.trans (le_of_eq ?_)
  unfold cwChunkAmbientTypeLoss cwChunkAmbientEntropyBase
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- **The zero-safe depth-generic inner growth datum.**

Identical to `cwChunkInnerGrowthDataOfMaximumEntropy` except that the reference profile may have
structural zeros; the ambient base is then `exp (mass * H)` rather than the (undefined-at-zero)
proportional entropy base.  This is the form the depth-four assembly needs. -/
noncomputable def cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hrefMass : 0 < WordType.profileMass reference)
    (hmaximum : WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K q depth)
      (WordType.normalizedProfileProbability reference hrefMass)) :
    CWTotalWeightInnerGrowthDataAtDepth K q depth reference
      (cwChunkAmbientEntropyBase reference)
      (cwChunkAmbientTypeLoss reference) where
  exponent k := WordType.profileMass reference * k - 1
  coarseWord k := cwChunkCanonicalCoarseWord K q depth reference k
  length_eq k hk := by
    have : 0 < WordType.profileMass reference * k := Nat.mul_pos hrefMass hk
    omega
  coarse_type k hk :=
    cwChunkCanonicalCoarseWord_multiplicity K q depth reference hrefMass k hk
  ambientBase_nonneg := (cwChunkAmbientEntropyBase_pos K q depth reference).le
  ambientLoss_pos k := cwChunkAmbientTypeLoss_pos K q depth reference k
  ambientLoss_subexponential := cwChunkAmbientTypeLoss_subexponential K q depth reference
  ambient_upper k hk := by
    refine card_cwTotalWeightLocalizedAmbientWords_le_entropyBase K q depth reference hrefMass
      hmaximum _ k hk ?_ _
    have : 0 < WordType.profileMass reference * k := Nat.mul_pos hrefMass hk
    omega

@[simp] theorem cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe_exponent
    (K : Type u) [CommRing K] (q depth : ℕ)
    (reference : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hrefMass : 0 < WordType.profileMass reference)
    (hmaximum : WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K q depth)
      (WordType.normalizedProfileProbability reference hrefMass)) (k : ℕ) :
    (cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe K q depth reference hrefMass
      hmaximum).exponent k = WordType.profileMass reference * k - 1 :=
  rfl

/-! ### The level-four index convention

The depth-four outer datum of `Examples/CoppersmithWinogradTotalWeightOuterDepthFour.lean` has
`n r = 19 * r - 1`, forced by `8 * 38 * r = 16 * (19 * r)`.  A growth datum matches that convention
exactly when its reference profile has mass `19`. -/

/-- A mass-`19` reference profile produces the depth-four outer index convention `19 * r - 1`. -/
theorem cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe_exponent_levelFour
    (K : Type u) [CommRing K]
    (reference : (cwChunkPartitionedTensor K 5 4).support → ℕ)
    (hmass : WordType.profileMass reference = 19)
    (hmaximum : WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K 5 4)
      (WordType.normalizedProfileProbability reference (by rw [hmass]; norm_num))) (r : ℕ) :
    (cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe K 5 4 reference
      (by rw [hmass]; norm_num) hmaximum).exponent r = 19 * r - 1 := by
  rw [cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe_exponent, hmass]

/-! ## The concrete constant-profile leaf -/

/-- The constant-`m` rational typed leaf of the depth-`depth` chunk partition, carrying the
canonical chunk dimensions.  Its normalized law is uniform, hence — by
`WordType.isMaximumEntropyInMappedFiber_const` — the entropy maximizer of its own three-leg mapped
fiber with no structural input. -/
noncomputable def cwChunkConstantLeaf
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q) (m : ℕ) (hm : 0 < m) :
    RationalTypedLeaf (cwChunkPartitionedTensor K q depth).support
      (fun _c : Leg ↦ PositiveWord CWBlock (2 ^ depth - 1)) where
  profile :=
    { alphabet := Finset.univ
      complete := fun i ↦ Finset.mem_univ i
      count := fun _ ↦ m
      count_pos := fun _ ↦ hm }
  coordinate := cwChunkCoordinate K q depth
  dimension := cwChunkConstituentDimension K q depth
  dimension_pos i c := cwChunkConstituentDimension_pos K q depth hq i c

@[simp] theorem cwChunkConstantLeaf_count
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q) (m : ℕ) (hm : 0 < m)
    (i : (cwChunkPartitionedTensor K q depth).support) :
    (cwChunkConstantLeaf K q depth hq m hm).profile.count i = m :=
  rfl

/-- The constant leaf carries exactly the canonical chunk dimensions, which is the hypothesis
`hdimension` of the level-four endpoint adapter. -/
theorem cwChunkConstantLeaf_dimension
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q) (m : ℕ) (hm : 0 < m)
    (i : (cwChunkPartitionedTensor K q depth).support) (c : Leg) :
    (cwChunkConstantLeaf K q depth hq m hm).dimension i c =
      cwChunkConstituentDimension K q depth i c :=
  rfl

/-- **The concrete depth-generic datum.**  A hypothesis-free `CWTotalWeightInnerGrowthDataAtDepth`
for the constant-`m` chunk leaf. -/
noncomputable def cwChunkConstantInnerGrowthData
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q) (m : ℕ) (hm : 0 < m) :
    CWTotalWeightInnerGrowthDataAtDepth K q depth
      (cwChunkConstantLeaf K q depth hq m hm).profile.count
      (WordType.proportionalEntropyBase
        (cwChunkConstantLeaf K q depth hq m hm).profile.count)
      (cwChunkAmbientLoss (cwChunkConstantLeaf K q depth hq m hm).profile.count) :=
  cwChunkInnerGrowthDataOfMaximumEntropy K q depth
    (cwChunkConstantLeaf K q depth hq m hm).profile.count (fun _ ↦ hm)
    (WordType.isMaximumEntropyInMappedFiber_const (cwChunkCoordinate K q depth) m hm _)

/-- The level-four constant-`19` leaf of the `CW₅` chunk partition. -/
noncomputable def cwChunkConstantLeafLevelFour (K : Type u) [CommRing K] :
    RationalTypedLeaf (cwChunkPartitionedTensor K 5 4).support
      (fun _c : Leg ↦ PositiveWord CWBlock (2 ^ 4 - 1)) :=
  cwChunkConstantLeaf K 5 4 (by norm_num) 19 (by norm_num)

/-- **The level-four inner growth datum**, at the certificate's parameters `q = 5`, `depth = 4`.
Its `ambient_upper` field is proved, not assumed. -/
noncomputable def cwChunkConstantInnerGrowthDataLevelFour (K : Type u) [CommRing K] :
    CWTotalWeightInnerGrowthDataAtDepth K 5 4
      (cwChunkConstantLeafLevelFour K).profile.count
      (WordType.proportionalEntropyBase (cwChunkConstantLeafLevelFour K).profile.count)
      (cwChunkAmbientLoss (cwChunkConstantLeafLevelFour K).profile.count) :=
  cwChunkConstantInnerGrowthData K 5 4 (by norm_num) 19 (by norm_num)

/-! ## The one-type chunk letter -/

/-- Product of a numerical parameter along a constant positive word. -/
theorem positiveWordProduct_const {I : Type*} [Fintype I]
    (x : I → ℕ) (r : ℕ) (i : I) :
    positiveWordProduct x r (positiveWordConst i r) = x i ^ (r + 1) := by
  induction r with
  | zero =>
      show x i = x i ^ 1
      exact (pow_one _).symm
  | succ r ih =>
      show positiveWordProduct x r (positiveWordConst i r) * x i = x i ^ (r + 1 + 1)
      rw [ih]
      exact (pow_succ _ _).symm

/-- The supported base CW block `cw011`, whose canonical matrix dimensions are `(1, 1, q)`. -/
def cwOneTypeBlock (K : Type u) [CommRing K] (q : ℕ) :
    (cwPartitionedTensor K q).support :=
  ⟨cw011, by
    change cw011 ∈ cwBlockSupport
    decide⟩

/-- The chunk letter all of whose `2 ^ depth` base blocks are `cw011`.  Its three canonical chunk
dimensions are `(1, 1, q ^ 2 ^ depth)`, so it is the maximal-volume letter of the chunk support. -/
noncomputable def cwChunkOneTypeWitness
    (K : Type u) [CommRing K] (q depth : ℕ) :
    (cwChunkPartitionedTensor K q depth).support := by
  classical
  refine ⟨positiveSupportWordBlockAddress
    (cwPartitionedTensor K q).support (2 ^ depth - 1)
    (positiveWordConst (cwOneTypeBlock K q) (2 ^ depth - 1)), ?_⟩
  change _ ∈ ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).support
  rw [(cwPartitionedTensor K q).positivePower_support_eq_image_positiveSupportWordBlockAddress]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- The base word recovered from the one-type chunk letter is the constant `cw011` word. -/
theorem cwChunkSupportedWordOfAddress_oneTypeWitness
    (K : Type u) [CommRing K] (q depth : ℕ) :
    cwChunkSupportedWordOfAddress K q depth (cwChunkOneTypeWitness K q depth) =
      positiveWordConst (cwOneTypeBlock K q) (2 ^ depth - 1) := by
  apply Tensor.positiveSupportWordBlockAddress_injective
    (cwPartitionedTensor K q).support (2 ^ depth - 1)
  rw [positiveSupportWordBlockAddress_cwChunkSupportedWordOfAddress]
  rfl

/-- Exact canonical chunk dimensions of the one-type chunk letter. -/
theorem cwChunkConstituentDimension_oneTypeWitness
    (K : Type u) [CommRing K] (q depth : ℕ) (c : Leg) :
    cwChunkConstituentDimension K q depth (cwChunkOneTypeWitness K q depth) c =
      cwBaseConstituentDimension q (cwOneTypeBlock K q) c ^ 2 ^ depth := by
  have hconst := positiveWordProduct_const
    (fun s : (cwPartitionedTensor K q).support ↦ cwBaseConstituentDimension q s c)
    (2 ^ depth - 1) (cwOneTypeBlock K q)
  rw [two_pow_sub_one_add_one] at hconst
  rw [cwChunkConstituentDimension, cwChunkSupportedWordOfAddress_oneTypeWitness]
  exact hconst

/-- The one-type chunk letter has rectangular volume exactly `q ^ 2 ^ depth`. -/
theorem cwChunk_oneTypeWitness_volume
    (K : Type u) [CommRing K] (q depth : ℕ) :
    cwChunkConstituentDimension K q depth (cwChunkOneTypeWitness K q depth) .X *
        cwChunkConstituentDimension K q depth (cwChunkOneTypeWitness K q depth) .Y *
        cwChunkConstituentDimension K q depth (cwChunkOneTypeWitness K q depth) .Z =
      q ^ 2 ^ depth := by
  rw [cwChunkConstituentDimension_oneTypeWitness, cwChunkConstituentDimension_oneTypeWitness,
    cwChunkConstituentDimension_oneTypeWitness]
  have hX : cwBaseConstituentDimension q (cwOneTypeBlock K q) .X = 1 := by
    show (cwConstituentDimensions q cw011).1 = 1
    simp
  have hY : cwBaseConstituentDimension q (cwOneTypeBlock K q) .Y = 1 := by
    show (cwConstituentDimensions q cw011).2.1 = 1
    simp
  have hZ : cwBaseConstituentDimension q (cwOneTypeBlock K q) .Z = q := by
    show (cwConstituentDimensions q cw011).2.2 = q
    simp
  rw [hX, hY, hZ]
  simp

/-! ## The exact dimension product of a canonical-dimension leaf -/

/-- **Any** rational typed leaf carrying the canonical chunk dimensions has rectangular volume at
least the one-type chunk letter's volume raised to that letter's own multiplicity.

Every chunk letter has volume at least `1`, so a single letter of the profile already forces the
bound; the all-`cw011` letter is the one with the largest volume, `q ^ 2 ^ depth`.  This is the
form the volume floor needs, and it is independent of how sparse the leaf's profile is. -/
theorem cwChunk_dimensionProduct_ge_oneTypeWitness
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c) :
    (q ^ 2 ^ depth) ^ leaf.profile.count (cwChunkOneTypeWitness K q depth) ≤
      leaf.dimensionProduct .X * leaf.dimensionProduct .Y * leaf.dimensionProduct .Z := by
  classical
  have hprod : ∀ c : Leg, leaf.dimensionProduct c =
      ∏ i, cwChunkConstituentDimension K q depth i c ^ leaf.profile.count i := by
    intro c
    rw [RationalTypedLeaf.dimensionProduct, leaf.profile.alphabet_eq_univ]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [hdimension]
  rw [hprod, hprod, hprod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  have hcombine : ∀ i : (cwChunkPartitionedTensor K q depth).support,
      cwChunkConstituentDimension K q depth i .X ^ leaf.profile.count i *
          cwChunkConstituentDimension K q depth i .Y ^ leaf.profile.count i *
          cwChunkConstituentDimension K q depth i .Z ^ leaf.profile.count i =
        (cwChunkConstituentDimension K q depth i .X *
          cwChunkConstituentDimension K q depth i .Y *
          cwChunkConstituentDimension K q depth i .Z) ^ leaf.profile.count i := by
    intro i
    rw [mul_pow, mul_pow]
  have hone : ∀ i ∈ (Finset.univ : Finset (cwChunkPartitionedTensor K q depth).support),
      1 ≤ cwChunkConstituentDimension K q depth i .X ^ leaf.profile.count i *
          cwChunkConstituentDimension K q depth i .Y ^ leaf.profile.count i *
          cwChunkConstituentDimension K q depth i .Z ^ leaf.profile.count i := by
    intro i _
    exact Nat.one_le_iff_ne_zero.mpr (by
      have hX := cwChunkConstituentDimension_pos K q depth hq i .X
      have hY := cwChunkConstituentDimension_pos K q depth hq i .Y
      have hZ := cwChunkConstituentDimension_pos K q depth hq i .Z
      positivity)
  have hsingle := Finset.single_le_prod' hone
    (Finset.mem_univ (cwChunkOneTypeWitness K q depth))
  refine le_trans ?_ hsingle
  rw [hcombine, cwChunk_oneTypeWitness_volume]

/-- The constant-`m` leaf's three dimension products multiply to at least the `m`-th power of the
one-type chunk letter's volume. -/
theorem cwChunkConstantLeaf_dimensionProduct_ge
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q) (m : ℕ) (hm : 0 < m) :
    (q ^ 2 ^ depth) ^ m ≤
      (cwChunkConstantLeaf K q depth hq m hm).dimensionProduct .X *
        (cwChunkConstantLeaf K q depth hq m hm).dimensionProduct .Y *
        (cwChunkConstantLeaf K q depth hq m hm).dimensionProduct .Z :=
  cwChunk_dimensionProduct_ge_oneTypeWitness K q depth hq
    (cwChunkConstantLeaf K q depth hq m hm) (fun _ _ ↦ rfl)

/-! ## The volume floor -/

set_option exponentiation.threshold 512 in
/-- `2 ^ (3 * 38 * v) ≤ 5 ^ 304` for every volume floor `v ≤ 6.0091024`.

The threshold `3755689/625000` is the floor hard-coded in
`MatrixMultiplication/Generated/TotalQuotientVolumeScalarData.lean` (and therefore used by
`MatrixMultiplication.TotalWeightVolumeEndpoint.volumeFloor`, which the level-four endpoint adapter
consumes).  It dominates the `C′` floor `15021/2500 = 6.0084` of
`MatrixMultiplication/TotalWeightAcceptanceFloors.lean`, so this single statement discharges both.

Numerically `3 * 38 * 6.0091024 = 685.03767` and `685.03767 * log 2 = 474.8323`, against
`304 * log 5 = 489.2691`; the certified enclosures `log 2 ≤ 0.6931471806`,
`log 5 ≥ 1.6094379123` of `Analysis/LogConstants.lean` leave a margin of about `14.4`.

The minimal admissible exponent is `295` at the `C′` floor (mean volume `6.00849814`) and `296` at
the older one; the leaf built here reaches `304` (mean volume `6.19181`), so it clears both floors
with room to spare rather than on the nose. -/
theorem two_rpow_le_five_pow_304 {v : ℝ} (hv : v ≤ 3755689 / 625000) :
    (2 : ℝ) ^ (3 * (38 : ℝ) * v) ≤ ((5 : ℕ) ^ (304 : ℕ) : ℝ) := by
  have hmono : (2 : ℝ) ^ (3 * (38 : ℝ) * v) ≤
      (2 : ℝ) ^ (3 * (38 : ℝ) * (3755689 / 625000)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    nlinarith
  refine hmono.trans ?_
  have hrpow : (2 : ℝ) ^ (3 * (38 : ℝ) * (3755689 / 625000)) =
      Real.exp (Real.log 2 * (3 * (38 : ℝ) * (3755689 / 625000))) :=
    Real.rpow_def_of_pos (by norm_num) _
  have hpow : ((5 : ℕ) ^ (304 : ℕ) : ℝ) =
      Real.exp (((304 : ℕ) : ℝ) * Real.log 5) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
    push_cast
    ring
  rw [hrpow, hpow]
  refine Real.exp_le_exp.mpr ?_
  have hlogTwo := Analysis.log_two_le_sharp
  have hlogFive := Analysis.log_five_ge_sharp
  push_cast
  nlinarith [hlogTwo, hlogFive]

set_option exponentiation.threshold 512 in
/-- **The volume floor, for every canonical-dimension depth-four leaf that puts multiplicity at
least `19` on the all-`cw011` chunk letter.**

This is the exact shape of the `hvolume` hypothesis of
`MatrixMultiplication.TotalWeightLeanEndpoint.omega_lt_236999_of_levelFourCanonicalInner`, at the
stride `38` of `MatrixMultiplication/TotalWeightAcceptanceFloors.lean` and for any volume floor at
most `3755689/625000`.  The dimension product is exact `Nat` arithmetic; only the base-two
comparison is analytic.

The hypothesis `19 ≤ count (one-type witness)` is exactly the chunk-alignment mass at depth four:
a mass-`19` profile concentrated on the maximal-volume chunk letter realizes it. -/
theorem cwChunkLevelFour_volumeFloor_of_oneTypeCount
    (K : Type u) [CommRing K]
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf (cwChunkPartitionedTensor K 5 4).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K 5 4 support c)
    (hcount : 19 ≤ leaf.profile.count (cwChunkOneTypeWitness K 5 4))
    {v : ℝ} (hv : v ≤ 3755689 / 625000) :
    (2 : ℝ) ^ (3 * (38 : ℝ) * v) ≤
      ((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
        leaf.dimensionProduct .Z : ℕ) : ℝ) := by
  have hleaf := cwChunk_dimensionProduct_ge_oneTypeWitness K 5 4 (by norm_num) leaf hdimension
  have hstep : ((5 : ℕ) ^ 2 ^ 4) ^ (19 : ℕ) ≤
      ((5 : ℕ) ^ 2 ^ 4) ^ leaf.profile.count (cwChunkOneTypeWitness K 5 4) :=
    Nat.pow_le_pow_right (by norm_num) hcount
  have hsplit : (5 : ℕ) ^ (304 : ℕ) = ((5 : ℕ) ^ 2 ^ 4) ^ (19 : ℕ) := by
    rw [← pow_mul]
    norm_num
  have hnat : (5 : ℕ) ^ (304 : ℕ) ≤
      leaf.dimensionProduct .X * leaf.dimensionProduct .Y * leaf.dimensionProduct .Z := by
    rw [hsplit]
    exact hstep.trans hleaf
  refine (two_rpow_le_five_pow_304 hv).trans ?_
  exact_mod_cast hnat

/-- The volume floor for the level-four constant-`19` leaf. -/
theorem cwChunkConstantLeafLevelFour_volumeFloor
    (K : Type u) [CommRing K] {v : ℝ} (hv : v ≤ 3755689 / 625000) :
    (2 : ℝ) ^ (3 * (38 : ℝ) * v) ≤
      (((cwChunkConstantLeafLevelFour K).dimensionProduct .X *
        (cwChunkConstantLeafLevelFour K).dimensionProduct .Y *
        (cwChunkConstantLeafLevelFour K).dimensionProduct .Z : ℕ) : ℝ) :=
  cwChunkLevelFour_volumeFloor_of_oneTypeCount K (cwChunkConstantLeafLevelFour K)
    (fun _ _ ↦ rfl) (le_refl 19) hv

/-- The `C′` volume floor `15021/2500 = 6.0084` of
`MatrixMultiplication/TotalWeightAcceptanceFloors.lean`, specialized. -/
theorem cwChunkConstantLeafLevelFour_acceptanceVolumeFloor (K : Type u) [CommRing K] :
    (2 : ℝ) ^ (3 * (38 : ℝ) * (15021 / 2500)) ≤
      (((cwChunkConstantLeafLevelFour K).dimensionProduct .X *
        (cwChunkConstantLeafLevelFour K).dimensionProduct .Y *
        (cwChunkConstantLeafLevelFour K).dimensionProduct .Z : ℕ) : ℝ) :=
  cwChunkConstantLeafLevelFour_volumeFloor K (by norm_num)

/-! ## The depth-four alignment obstruction

The depth-four outer datum has `n r = 19 * r - 1`.  This section proves that no growth datum built
over a *rational typed leaf of the full depth-four chunk support* can meet that convention: the
alphabet has `6 ^ 16` letters and `PositiveIntegralProfile.count_pos` forces one unit of mass per
letter, so the profile mass can never be `19`.
-/

/-- Cardinality of a positive word over a finite alphabet.  (Local restatement of
`fintypeCard_positiveWord`, to keep this module's import surface small.) -/
theorem fintypeCard_positiveWord_local (I : Type*) [Fintype I] (n : ℕ) :
    Fintype.card (PositiveWord I n) = Fintype.card I ^ (n + 1) := by
  calc
    Fintype.card (PositiveWord I n) = Fintype.card (Fin (n + 1) → I) :=
      Fintype.card_congr (positiveWordEquiv I n)
    _ = Fintype.card I ^ (n + 1) := by
      rw [Fintype.card_fun, Fintype.card_fin]

/-- The base CW partition has exactly six supported blocks. -/
theorem card_cwPartitionedTensor_support (K : Type u) [CommRing K] (q : ℕ) :
    Fintype.card (cwPartitionedTensor K q).support = 6 := by
  classical
  rw [Fintype.card_coe]
  show cwBlockSupport.card = 6
  decide

/-- The depth-`depth` chunk support has exactly `6 ^ 2 ^ depth` letters. -/
theorem card_cwChunkPartitionedTensor_support
    (K : Type u) [CommRing K] (q depth : ℕ) :
    Fintype.card (cwChunkPartitionedTensor K q depth).support = 6 ^ 2 ^ depth := by
  classical
  rw [Fintype.card_coe]
  show ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).support.card = _
  rw [(cwPartitionedTensor K q).positivePower_support_eq_image_positiveSupportWordBlockAddress,
    Finset.card_image_of_injective _
      (Tensor.positiveSupportWordBlockAddress_injective
        (cwPartitionedTensor K q).support (2 ^ depth - 1)),
    Finset.card_univ, fintypeCard_positiveWord_local, card_cwPartitionedTensor_support,
    two_pow_sub_one_add_one]

/-- A rational typed leaf spends at least one unit of profile mass on every letter of its
alphabet, so its mass is at least the alphabet size. -/
theorem card_le_profileMass_of_rationalTypedLeaf
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf (cwChunkPartitionedTensor K q depth).support C) :
    Fintype.card (cwChunkPartitionedTensor K q depth).support ≤
      WordType.profileMass leaf.profile.count := by
  classical
  calc
    Fintype.card (cwChunkPartitionedTensor K q depth).support =
        ∑ _i : (cwChunkPartitionedTensor K q depth).support, 1 := by simp
    _ ≤ ∑ i, leaf.profile.count i :=
      Finset.sum_le_sum fun i _ ↦ leaf.profile.count_pos i

/-- **The depth-four alignment obstruction.**

`omega_lt_236999_of_levelFourCanonicalInner` requires `outer.n r = growth.exponent r`, and the
depth-four outer datum has `n r = 19 * r - 1`; by `length_eq` that forces
`profileMass leaf.profile.count = 19`.  But the depth-four chunk alphabet has `6 ^ 16` letters and a
`PositiveIntegralProfile` is strictly positive on all of them.  Hence no growth datum over a
full-support depth-four leaf can match the outer index convention. -/
theorem no_levelFour_leaf_growthData_matches_outerExponent
    (K : Type u) [CommRing K]
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf (cwChunkPartitionedTensor K 5 4).support C)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (growth : CWTotalWeightInnerGrowthDataAtDepth K 5 4 leaf.profile.count
      ambientBase ambientLoss) :
    growth.exponent 1 ≠ 19 * 1 - 1 := by
  intro hexponent
  have hlen := growth.length_eq 1 Nat.one_pos
  rw [hexponent] at hlen
  have hcard := card_le_profileMass_of_rationalTypedLeaf K 5 4 leaf
  rw [card_cwChunkPartitionedTensor_support] at hcard
  omega

end AlgebraicComplexity.Examples
