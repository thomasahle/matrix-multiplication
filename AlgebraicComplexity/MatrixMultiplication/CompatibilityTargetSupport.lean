import AlgebraicComplexity.MatrixMultiplication.FeatureCompatibilityContainment
import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibilityInterface

/-!
# Reconstructing support-correct compatibility targets

Compatibility target tables are exact integer counts.  Their intended source is a family of
complete-split profiles, whose types already guarantee that every nonzero word has the prescribed
total.  This module records the exact-profile side of that reconstruction and combines it with
`ExactSplitAvgFamily.RealizesTargets` for the pooled positive-region tables.

The resulting theorem proves `CompatibilityTargets.IsWeightSupported`; downstream compatibility
and hashing arguments therefore consume a theorem derived from the reconstructed profiles, not
an unchecked property of numerical tables.
-/

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open AlgebraicComplexity.Tensor

universe u

/-- Exact complete-split profiles for the three logical legs of every tagged coarse constituent.
The number of positions in a cell may depend on both the leg and the coarse constituent. -/
structure ExactCompatibilityProfileFamily (Part : Type u) (depth : ℕ) where
  samples : Leg → CoarseIndex Part → ℕ
  profile : ∀ c q,
    CompleteSplitProfile depth (q.get c) (samples c q)

namespace ExactCompatibilityProfileFamily

variable {Part : Type u} {depth : ℕ}

/-- Build the exact-profile family directly from certificate count tables plus their bounded
sum and structural-support checks. -/
def ofCounts
    (samples : Leg → CoarseIndex Part → ℕ)
    (counts : ∀ _c, CoarseIndex Part → SplitWord depth → ℕ)
    (hsum : ∀ c q, ∑ word, counts c q word = samples c q)
    (hsupported : ∀ c q word, counts c q word ≠ 0 →
      splitWordWeight word = q.get c) :
    ExactCompatibilityProfileFamily Part depth where
  samples := samples
  profile c q := CompleteSplitProfile.ofCounts
    (counts c q) (hsum c q) (hsupported c q)

@[simp] theorem ofCounts_profile_counts
    (samples : Leg → CoarseIndex Part → ℕ)
    (counts : ∀ _c, CoarseIndex Part → SplitWord depth → ℕ)
    (hsum : ∀ c q, ∑ word, counts c q word = samples c q)
    (hsupported : ∀ c q word, counts c q word ≠ 0 →
      splitWordWeight word = q.get c)
    (c : Leg) (q : CoarseIndex Part) (word : SplitWord depth) :
    ((ofCounts samples counts hsum hsupported).profile c q).counts word =
      counts c q word :=
  rfl

/-- The exact profiles reproduce the three exact tables stored by a compatibility target. -/
def RealizesTargets (data : ExactCompatibilityProfileFamily Part depth)
    (targets : CompatibilityTargets Part depth) : Prop :=
  (∀ q word, (data.profile .X q).counts word = targets.xExact q word) ∧
    (∀ q word, (data.profile .Y q).counts word = targets.yExact q word) ∧
    (∀ q word, (data.profile .Z q).counts word = targets.zExact q word)

/-- Exact profile reconstruction proves support of the `X` target table. -/
theorem isXWeightSupported_of_realizesTargets
    (data : ExactCompatibilityProfileFamily Part depth)
    (targets : CompatibilityTargets Part depth)
    (hdata : data.RealizesTargets targets) :
    targets.IsXWeightSupported := by
  intro q word hpositive
  have hnonzero : (data.profile .X q).counts word ≠ 0 := by
    rw [hdata.1 q word]
    exact Nat.ne_of_gt hpositive
  simpa [CoarseIndex.get] using (data.profile .X q).supported word hnonzero

/-- Exact profile reconstruction proves support of the exact part of the `Y` target table. -/
theorem yExact_weight_eq_of_realizesTargets
    (data : ExactCompatibilityProfileFamily Part depth)
    (targets : CompatibilityTargets Part depth)
    (hdata : data.RealizesTargets targets)
    (q : CoarseIndex Part) (word : SplitWord depth)
    (hpositive : 0 < targets.yExact q word) :
    splitWordWeight word = q.y := by
  have hnonzero : (data.profile .Y q).counts word ≠ 0 := by
    rw [hdata.2.1 q word]
    exact Nat.ne_of_gt hpositive
  simpa [CoarseIndex.get] using (data.profile .Y q).supported word hnonzero

/-- Exact profile reconstruction proves support of the exact part of the `Z` target table. -/
theorem zExact_weight_eq_of_realizesTargets
    (data : ExactCompatibilityProfileFamily Part depth)
    (targets : CompatibilityTargets Part depth)
    (hdata : data.RealizesTargets targets)
    (q : CoarseIndex Part) (word : SplitWord depth)
    (hpositive : 0 < targets.zExact q word) :
    splitWordWeight word = q.z := by
  have hnonzero : (data.profile .Z q).counts word ≠ 0 := by
    rw [hdata.2.2 q word]
    exact Nat.ne_of_gt hpositive
  simpa [CoarseIndex.get] using (data.profile .Z q).supported word hnonzero

/-- Exact and pooled reconstructions together prove support of every `Y` target table. -/
theorem isYWeightSupported_of_realizesTargets
    (data : ExactCompatibilityProfileFamily Part depth)
    (pooled : ExactSplitAvgFamily Part depth)
    (targets : CompatibilityTargets Part depth)
    (hdata : data.RealizesTargets targets)
    (hpooled : pooled.RealizesTargets targets) :
    targets.IsYWeightSupported := by
  constructor
  · exact data.yExact_weight_eq_of_realizesTargets targets hdata
  · intro part total word hpositive
    have hnonzero : (pooled.y part total).positive.counts word ≠ 0 := by
      rw [(hpooled.1 part total word).2]
      exact Nat.ne_of_gt hpositive
    exact (pooled.y part total).positive.supported word hnonzero

/-- Exact and pooled reconstructions together prove support of every `Z` target table. -/
theorem isZWeightSupported_of_realizesTargets
    (data : ExactCompatibilityProfileFamily Part depth)
    (pooled : ExactSplitAvgFamily Part depth)
    (targets : CompatibilityTargets Part depth)
    (hdata : data.RealizesTargets targets)
    (hpooled : pooled.RealizesTargets targets) :
    targets.IsZWeightSupported := by
  constructor
  · exact data.zExact_weight_eq_of_realizesTargets targets hdata
  · intro part total word hpositive
    have hnonzero : (pooled.z part total).positive.counts word ≠ 0 := by
      rw [(hpooled.2 part total word).2]
      exact Nat.ne_of_gt hpositive
    exact (pooled.z part total).positive.supported word hnonzero

/-- Complete exact reconstruction forces every compatibility target table to be supported on
the coarse coordinate encoded by its cell. -/
theorem isWeightSupported_of_realizesTargets
    (data : ExactCompatibilityProfileFamily Part depth)
    (pooled : ExactSplitAvgFamily Part depth)
    (targets : CompatibilityTargets Part depth)
    (hdata : data.RealizesTargets targets)
    (hpooled : pooled.RealizesTargets targets) :
    targets.IsWeightSupported :=
  ⟨data.isXWeightSupported_of_realizesTargets targets hdata,
    data.isYWeightSupported_of_realizesTargets pooled targets hdata hpooled,
    data.isZWeightSupported_of_realizesTargets pooled targets hdata hpooled⟩

end ExactCompatibilityProfileFamily

end MoreAsymmetryCompatibility
end AlgebraicComplexity
