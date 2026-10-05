/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.BetaFourShardedContributions

/-!
# Reflected input checks for dense beta-four band certificates

This leaf module separates the untrusted serialized form and its Boolean checker from the generic
dense-band arithmetic.  Generated clients can change certificate encoding without invalidating
the much larger sparse-routing closure.  A successful raw-band check validates interval order,
the hard 64-position boundary, payload length, and every semantic value; a second lightweight
check validates continuity of an already checked band list.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

namespace BetaFourRoutedContribution

/-- Untrusted serialized input for one bounded dense target band.

Unlike `DenseBandCertificate`, this record contains no proofs. Generated clients serialize only
this data and establish one named Boolean-check equation; `RawDenseBand.toCertificate` is the
small proved checker that turns the equation into the semantic certificate.
-/
structure RawDenseBand where
  lower : ℕ
  upper : ℕ
  values : List ℕ
  deriving DecidableEq, Repr

namespace RawDenseBand

/-- Semantic validity predicate reflected by `check`.

It records the interval order, the hard 64-position checking boundary, the exact payload length,
and equality with the pointwise sparse-row sum.
-/
def IsValid (partials : List (List BetaFourRoutedContribution)) (raw : RawDenseBand) : Prop :=
  raw.lower ≤ raw.upper ∧
    raw.upper - raw.lower ≤ 64 ∧
    raw.values.length = raw.upper - raw.lower ∧
    raw.values = (List.range' raw.lower (raw.upper - raw.lower)).map fun position ↦
      (partials.map fun row ↦ sparseNumeratorAt row position).sum

instance (partials : List (List BetaFourRoutedContribution)) (raw : RawDenseBand) :
    Decidable (raw.IsValid partials) := by
  unfold IsValid
  infer_instance

/-- Executable bounded checker for an untrusted dense-band payload. -/
def check (partials : List (List BetaFourRoutedContribution)) (raw : RawDenseBand) : Bool :=
  decide (raw.IsValid partials)

/-- A successful Boolean check yields the full semantic dense-band certificate.

Proof sketch: reflection turns `check = true` into the four conjuncts of `IsValid`. The semantic
certificate retains the interval order and exact value equality; the raw validity theorem also
records the checker-specific width and length bounds.
-/
def toCertificate (raw : RawDenseBand)
    (partials : List (List BetaFourRoutedContribution))
    (hcheck : raw.check partials = true) : DenseBandCertificate partials := by
  have hdecide : decide (raw.IsValid partials) = true := by
    simpa only [check] using hcheck
  have hvalid : raw.IsValid partials := of_decide_eq_true hdecide
  exact
    { lower := raw.lower
      upper := raw.upper
      bounds := hvalid.1
      values := raw.values
      values_eq := hvalid.2.2.2 }

@[simp] theorem toCertificate_lower (raw : RawDenseBand)
    (partials : List (List BetaFourRoutedContribution)) (hcheck : raw.check partials = true) :
    (raw.toCertificate partials hcheck).lower = raw.lower := rfl

@[simp] theorem toCertificate_upper (raw : RawDenseBand)
    (partials : List (List BetaFourRoutedContribution)) (hcheck : raw.check partials = true) :
    (raw.toCertificate partials hcheck).upper = raw.upper := rfl

@[simp] theorem toCertificate_values (raw : RawDenseBand)
    (partials : List (List BetaFourRoutedContribution)) (hcheck : raw.check partials = true) :
    (raw.toCertificate partials hcheck).values = raw.values := rfl

/-- A successful raw check exposes the kernel-verified 64-position boundary. -/
theorem width_le (raw : RawDenseBand) (partials : List (List BetaFourRoutedContribution))
    (hcheck : raw.check partials = true) : raw.upper - raw.lower ≤ 64 := by
  have hdecide : decide (raw.IsValid partials) = true := by
    simpa only [check] using hcheck
  exact (of_decide_eq_true hdecide : raw.IsValid partials).2.1

/-- A successful raw check exposes the exact serialized payload length. -/
theorem values_length (raw : RawDenseBand) (partials : List (List BetaFourRoutedContribution))
    (hcheck : raw.check partials = true) : raw.values.length = raw.upper - raw.lower := by
  have hdecide : decide (raw.IsValid partials) = true := by
    simpa only [check] using hcheck
  exact (of_decide_eq_true hdecide : raw.IsValid partials).2.2.1

end RawDenseBand

namespace DenseBandCover

/-- Pure endpoint-layout predicate for a list of already checked dense bands. -/
def IsLayout {partials : List (List BetaFourRoutedContribution)} :
    ℕ → ℕ → List (DenseBandCertificate partials) → Prop
  | start, limit, [] => start = limit
  | start, limit, certificate :: bands =>
      certificate.lower = start ∧ IsLayout certificate.upper limit bands

instance {partials : List (List BetaFourRoutedContribution)}
    (start limit : ℕ) (bands : List (DenseBandCertificate partials)) :
    Decidable (IsLayout start limit bands) := by
  induction bands generalizing start with
  | nil =>
      simp only [IsLayout]
      infer_instance
  | cons certificate bands ih =>
      simp only [IsLayout]
      letI := ih certificate.upper
      infer_instance

/-- Executable checker that dense bands are consecutive and cover exactly `[start, limit)`. -/
def layoutCheck {partials : List (List BetaFourRoutedContribution)}
    (start limit : ℕ) (bands : List (DenseBandCertificate partials)) : Bool :=
  decide (IsLayout start limit bands)

/-- A successful layout check constructs the consecutive dense-band cover.

Proof sketch: reflect the Boolean result to `IsLayout`, then recurse through the band list. Each
head equality supplies `DenseBandCover.cons`; the empty case supplies `DenseBandCover.nil`.
-/
theorem of_layoutCheck_eq_true {partials : List (List BetaFourRoutedContribution)}
    {start limit : ℕ} {bands : List (DenseBandCertificate partials)}
    (hcheck : layoutCheck start limit bands = true) :
    DenseBandCover partials start limit bands := by
  have hdecide : decide (IsLayout start limit bands) = true := by
    simpa only [layoutCheck] using hcheck
  have hlayout : IsLayout start limit bands := of_decide_eq_true hdecide
  clear hcheck hdecide
  induction bands generalizing start with
  | nil =>
      simp only [IsLayout] at hlayout
      subst limit
      exact DenseBandCover.nil start
  | cons certificate bands ih =>
      simp only [IsLayout] at hlayout
      exact DenseBandCover.cons certificate bands hlayout.1 (ih hlayout.2)

end DenseBandCover

end BetaFourRoutedContribution

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
