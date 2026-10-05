/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogFormDefs

set_option autoImplicit false

/-!
# Fused accumulation of weighted entropy rows

Large generated entropy certificates often start with a probability row containing hundreds of
atoms, even though the row uses only two or three distinct probability numerators.  Constructing
one logarithmic term per atom and normalizing the resulting list makes Lean materialize a large
intermediate expression which has no mathematical significance.

This definition-only module performs the equivalent calculation in one pass.  Every atom is
inserted immediately into the small argument-indexed coefficient list, so the live accumulator is
bounded by the number of distinct numerators rather than by the alphabet size.  It imports only
the executable signed-log syntax: generated exact checkers do not load real logarithms, entropy,
or tactics.

The certificate-facing representation stores one bucket for each
`(probability numerator, feature)` pair, together with its multiplicity.  It is therefore compact
before Lean sees it; the executable fold merely combines the few buckets which share a logarithm
argument.
-/

namespace MatrixMultiplication.SignedDyadicLogForm

/-- One bucket of a weighted entropy row.

`numerator` is the shared dyadic probability numerator, `feature` is an integral statistic such as
the number of middle coordinates in a constituent address, and `multiplicity` is the number of
atoms having that pair. -/
structure WeightedBucket where
  numerator : Nat
  feature : Nat
  multiplicity : Nat
  deriving DecidableEq, Repr

namespace WeightedBucket

/-- The negative entropy term contributed by one bucket. -/
def entropyTerm (scale : Nat) (bucket : WeightedBucket) : Term :=
  ⟨bucket.numerator,
    -((scale * bucket.numerator * bucket.multiplicity : Nat) : Int)⟩

end WeightedBucket

namespace Form

/-- Sum of numerator-weighted integral features in one bucketed row. -/
def weightedFeatureSum (buckets : List WeightedBucket) : Nat :=
  (buckets.map fun bucket ↦
    bucket.multiplicity * bucket.numerator * bucket.feature).sum

/-- Insert every atom's entropy coefficient immediately into a compact coefficient list.

The result remains sorted by logarithm argument because `Form.insert` preserves that invariant.
More importantly for generated proofs, repeated arguments are combined after every atom, so this
fold never builds the expanded term list. -/
def accumulateEntropyTerms (scale : Nat) (buckets : List WeightedBucket) : List Term :=
  buckets.foldr (fun bucket terms ↦ insert (bucket.entropyTerm scale) terms) []

/-- The literal one-term-per-atom form represented by a weighted entropy row.

This definition records the mathematical reference expression.  Generated checkers should reduce
`compactWeightedRow`, not this expanded form. -/
def expandedWeightedRow (constantNumerator featureArgument scale : Nat)
    (buckets : List WeightedBucket) : Form :=
  ⟨constantNumerator,
    ⟨featureArgument, (scale * weightedFeatureSum buckets : Nat)⟩ ::
      buckets.map (WeightedBucket.entropyTerm scale)⟩

/-- Fused exact form for a weighted entropy row.

The positive feature term is inserted into the same small coefficient list, so it is combined
correctly when `featureArgument` itself occurs as a probability numerator. -/
def compactWeightedRow (constantNumerator featureArgument scale : Nat)
    (buckets : List WeightedBucket) : Form :=
  ⟨constantNumerator,
    insert
      ⟨featureArgument, (scale * weightedFeatureSum buckets : Nat)⟩
      (accumulateEntropyTerms scale buckets)⟩

/-- The fused atom fold is the ordinary normalizer applied after mapping atoms to terms.

Proof sketch: structural induction fuses `List.map` with `List.foldr`; both cons branches insert
the same head term into the induction hypothesis. -/
theorem accumulateEntropyTerms_eq_normalizeTerms_map (scale : Nat)
    (buckets : List WeightedBucket) :
    accumulateEntropyTerms scale buckets =
      normalizeTerms (buckets.map (WeightedBucket.entropyTerm scale)) := by
  induction buckets with
  | nil => rfl
  | cons bucket buckets ih =>
      change
        insert (bucket.entropyTerm scale) (accumulateEntropyTerms scale buckets) =
          insert (bucket.entropyTerm scale)
            (normalizeTerms (buckets.map (WeightedBucket.entropyTerm scale)))
      rw [ih]

/-- Fused accumulation computes exactly the ordinary normalization of the expanded row.

Human-readable statement: the compact implementation changes only when intermediate list cells
are created; its final exact form is the existing canonical normalization of the mathematical
one-term-per-atom expression.

Proof sketch: both sides right-fold the same `Form.insert` operation over the same atom terms.  The
preceding structural lemma fuses `List.map` with that fold; the remaining equality holds by
reduction. -/
theorem compactWeightedRow_eq_normalize
    (constantNumerator featureArgument scale : Nat) (buckets : List WeightedBucket) :
    compactWeightedRow constantNumerator featureArgument scale buckets =
      normalize (expandedWeightedRow constantNumerator featureArgument scale buckets) := by
  rw [compactWeightedRow, expandedWeightedRow, normalize,
    accumulateEntropyTerms_eq_normalizeTerms_map]
  rfl

end Form

end MatrixMultiplication.SignedDyadicLogForm
