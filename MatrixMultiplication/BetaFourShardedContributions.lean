/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.BetaFourSparseContributions

/-!
# Compositional sparse certificates for beta-four routes

`BetaFourSparseContributions` verifies one canonical sparse row.  Large generated parents should
not establish that row with one closed reduction over every routed contribution.  This module
provides the compositional boundary used instead:

* source rows are grouped into route chunks whose normalizations are checked independently;
* each normalized chunk is restricted to consecutive target bands;
* pieces in one band are combined through a trace of binary sparse merges;
* consecutive canonical bands are assembled by ordinary theorems.

The final soundness theorem recovers the dense routed semantics without reducing the complete
source flatten or final canonical row.  It also composes per-chunk `AllTargetsBelow` checks, so an
absent-`idxOf` sentinel cannot hide in a larger padded row.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

open MatrixMultiplication.DyadicEntropyForm

namespace BetaFourRoutedContribution

/-- Keep exactly the sparse contributions whose targets lie in `[lower, upper)`. -/
def restrictSparse (lower upper : ℕ) :
    List BetaFourRoutedContribution → List BetaFourRoutedContribution
  | [] => []
  | contribution :: tail =>
      if lower ≤ contribution.target ∧ contribution.target < upper then
        contribution :: restrictSparse lower upper tail
      else restrictSparse lower upper tail

/-- Restricting to a band preserves sparse evaluation at a position inside that band. -/
theorem sparseNumeratorAt_restrictSparse_of_mem
    (lower upper position : ℕ) (row : List BetaFourRoutedContribution)
    (hlower : lower ≤ position) (hupper : position < upper) :
    sparseNumeratorAt (restrictSparse lower upper row) position =
      sparseNumeratorAt row position := by
  induction row with
  | nil => rfl
  | cons head tail ih =>
      by_cases hband : lower ≤ head.target ∧ head.target < upper
      · by_cases htarget : head.target = position
        · subst position
          simp [restrictSparse, sparseNumeratorAt, hband, ih]
        · simp [restrictSparse, sparseNumeratorAt, hband, htarget, ih]
      · have htarget : head.target ≠ position := by
          intro heq
          subst position
          exact hband ⟨hlower, hupper⟩
        simp [restrictSparse, sparseNumeratorAt, hband, htarget, ih]

/-- A canonical row evaluates to zero strictly before its lower target bound. -/
theorem IsCanonicalFrom.sparseNumeratorAt_eq_zero_of_lt_start
    {start limit position : ℕ} {row : List BetaFourRoutedContribution}
    (hcanonical : IsCanonicalFrom start limit row) (hposition : position < start) :
    sparseNumeratorAt row position = 0 := by
  induction row generalizing start with
  | nil => rfl
  | cons head tail ih =>
      simp only [IsCanonicalFrom] at hcanonical
      rcases hcanonical with ⟨hstart, hlimit, hpositive, htail⟩
      have hne : head.target ≠ position := by omega
      simp only [sparseNumeratorAt, hne, if_false, Nat.zero_add]
      exact ih htail (by omega)

/-- A canonical row evaluates to zero at and beyond its upper target bound. -/
theorem IsCanonicalFrom.sparseNumeratorAt_eq_zero_of_limit_le
    {start limit position : ℕ} {row : List BetaFourRoutedContribution}
    (hcanonical : IsCanonicalFrom start limit row) (hposition : limit ≤ position) :
    sparseNumeratorAt row position = 0 := by
  induction row generalizing start with
  | nil => rfl
  | cons head tail ih =>
      simp only [IsCanonicalFrom] at hcanonical
      rcases hcanonical with ⟨hstart, hlimit, hpositive, htail⟩
      have hne : head.target ≠ position := by omega
      simp only [sparseNumeratorAt, hne, if_false, Nat.zero_add]
      exact ih htail

/-- Lowering the initial bound preserves canonicality. -/
theorem IsCanonicalFrom.mono_start {earlier start limit : ℕ}
    {row : List BetaFourRoutedContribution} (hcanonical : IsCanonicalFrom start limit row)
    (hearlier : earlier ≤ start) : IsCanonicalFrom earlier limit row := by
  cases row with
  | nil => trivial
  | cons head tail =>
      simp only [IsCanonicalFrom] at hcanonical ⊢
      exact ⟨le_trans hearlier hcanonical.1, hcanonical.2⟩

/-- Consecutive canonical rows concatenate to a canonical row over the combined interval.

Proof sketch: targets in the left row are below `middle`; targets in the right row start at
`middle`.  Induction through the left row therefore preserves strict order at the join.
-/
theorem IsCanonicalFrom.append {start middle limit : ℕ}
    {left right : List BetaFourRoutedContribution}
    (hleft : IsCanonicalFrom start middle left)
    (hright : IsCanonicalFrom middle limit right)
    (hstart : start ≤ middle) (hmiddle : middle ≤ limit) :
    IsCanonicalFrom start limit (left ++ right) := by
  induction left generalizing start with
  | nil =>
      simpa using hright.mono_start hstart
  | cons head tail ih =>
      simp only [IsCanonicalFrom] at hleft ⊢
      rcases hleft with ⟨hheadStart, hheadMiddle, hheadPositive, htail⟩
      refine ⟨hheadStart, lt_of_lt_of_le hheadMiddle hmiddle, hheadPositive, ?_⟩
      exact ih htail (by omega)

/-- A trace witnessing a left fold of binary sparse merges.

Each constructor exposes only one merge equation.  Generated clients can therefore check a
sequence of bounded rows without asking the kernel to normalize the complete fold at once.
-/
inductive MergeTrace : List BetaFourRoutedContribution →
    List (List BetaFourRoutedContribution) → List BetaFourRoutedContribution → Prop
  | nil (accumulator) : MergeTrace accumulator [] accumulator
  | cons (accumulator piece next final : List BetaFourRoutedContribution)
      (pieces : List (List BetaFourRoutedContribution))
      (step : mergeSparse accumulator piece = next)
      (tail : MergeTrace next pieces final) :
      MergeTrace accumulator (piece :: pieces) final

/-- A merge trace represents the pointwise sum of its initial row and all merged pieces. -/
theorem MergeTrace.sparseNumeratorAt {accumulator final : List BetaFourRoutedContribution}
    {pieces : List (List BetaFourRoutedContribution)}
    (htrace : MergeTrace accumulator pieces final) (position : ℕ) :
    sparseNumeratorAt final position =
      sparseNumeratorAt accumulator position +
        (pieces.map fun row ↦ sparseNumeratorAt row position).sum := by
  induction htrace with
  | nil accumulator => simp
  | cons accumulator piece next final pieces step tail ih =>
      rw [ih, ← step, sparseNumeratorAt_mergeSparse]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Independently checked normalizations sum to the source chunks' flattened routed numerator. -/
theorem sum_sparseNumeratorAt_eq_numeratorAt_flatten_of_forall₂
    {chunks : List (List (List (Option BetaFourRoutedContribution)))}
    {partials : List (List BetaFourRoutedContribution)}
    (hnormalized : List.Forall₂
      (fun chunk normalized ↦ canonicalizeRows chunk = normalized) chunks partials)
    (position : ℕ) :
    (partials.map fun row ↦ sparseNumeratorAt row position).sum =
      numeratorAt chunks.flatten.flatten position := by
  induction hnormalized with
  | nil => rfl
  | cons heq htail ih =>
      simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.flatten_append]
      rw [← heq, sparseNumeratorAt_canonicalizeRows, ih, numeratorAt_append]

/-- Per-chunk target bounds compose to a target bound for the complete flatten. -/
theorem AllTargetsBelow.append {limit : ℕ}
    {left right : List (Option BetaFourRoutedContribution)}
    (hleft : AllTargetsBelow limit left) (hright : AllTargetsBelow limit right) :
    AllTargetsBelow limit (left ++ right) := by
  induction left with
  | nil => simpa using hright
  | cons head tail ih =>
      cases head with
      | none =>
          simp only [AllTargetsBelow] at hleft ⊢
          exact ih hleft
      | some head =>
          simp only [AllTargetsBelow] at hleft ⊢
          exact ⟨hleft.1, ih hleft.2⟩

/-- A `Forall` family of target-bounded route chunks has a target-bounded complete flatten. -/
theorem AllTargetsBelow.flatten_of_forall {limit : ℕ}
    {chunks : List (List (Option BetaFourRoutedContribution))}
    (hchunks : chunks.Forall (AllTargetsBelow limit)) :
    AllTargetsBelow limit chunks.flatten := by
  induction chunks with
  | nil => trivial
  | cons chunk chunks ih =>
      rcases (List.forall_cons (AllTargetsBelow limit) chunk chunks).mp hchunks with
        ⟨hchunk, hchunks⟩
      simpa only [List.flatten_cons] using hchunk.append (ih hchunks)

/-- Per-outer-chunk bounds compose through two list-flattening layers. -/
theorem AllTargetsBelow.flatten₂_of_forall {limit : ℕ}
    {chunks : List (List (List (Option BetaFourRoutedContribution)))}
    (hchunks : chunks.Forall fun chunk ↦ AllTargetsBelow limit chunk.flatten) :
    AllTargetsBelow limit chunks.flatten.flatten := by
  induction chunks with
  | nil => trivial
  | cons chunk chunks ih =>
      rcases (List.forall_cons
        (fun rest ↦ AllTargetsBelow limit rest.flatten) chunk chunks).mp hchunks with
        ⟨hchunk, hchunks⟩
      simpa only [List.flatten_cons, List.flatten_append] using
        hchunk.append (ih hchunks)

/-- Band restriction preserves the sum of sparse evaluations at an in-band position. -/
theorem sum_sparseNumeratorAt_eq_of_restricted_forall₂
    {lower upper position : ℕ}
    {sources pieces : List (List BetaFourRoutedContribution)}
    (hrestricted : List.Forall₂
      (fun source piece ↦ restrictSparse lower upper source = piece) sources pieces)
    (hlower : lower ≤ position) (hupper : position < upper) :
    (pieces.map fun row ↦ sparseNumeratorAt row position).sum =
      (sources.map fun row ↦ sparseNumeratorAt row position).sum := by
  induction hrestricted with
  | nil => rfl
  | cons heq htail ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← heq,
        sparseNumeratorAt_restrictSparse_of_mem lower upper position _ hlower hupper,
        ih]

/-- Optional band pieces preserve the in-band sum after absent pieces are discarded. -/
theorem sum_sparseNumeratorAt_filterMap_eq_of_restricted_forall₂
    {lower upper position : ℕ}
    {sources : List (List BetaFourRoutedContribution)}
    {results : List (Option (List BetaFourRoutedContribution))}
    (hrestricted : List.Forall₂
      (fun source result ↦ restrictSparse lower upper source = result.getD []) sources results)
    (hlower : lower ≤ position) (hupper : position < upper) :
    ((results.filterMap id).map fun row ↦ sparseNumeratorAt row position).sum =
      (sources.map fun row ↦ sparseNumeratorAt row position).sum := by
  induction sources generalizing results with
  | nil =>
      cases results with
      | nil => rfl
      | cons result results => cases hrestricted
  | cons source sources ih =>
      cases results with
      | nil => cases hrestricted
      | cons result results =>
          cases hrestricted with
          | cons hhead htail =>
              cases result with
              | none =>
                  have hhead' : restrictSparse lower upper source = [] := by
                    simpa using hhead
                  have hsourceZero : sparseNumeratorAt source position = 0 := by
                    rw [← sparseNumeratorAt_restrictSparse_of_mem
                      lower upper position source hlower hupper, hhead']
                    rfl
                  simpa [hsourceZero] using ih htail
              | some piece =>
                  have hhead' : restrictSparse lower upper source = piece := by
                    simpa using hhead
                  simp only [List.filterMap_cons, id_eq,
                    List.map_cons, List.sum_cons]
                  rw [← hhead',
                    sparseNumeratorAt_restrictSparse_of_mem
                      lower upper position source hlower hupper]
                  congr 1
                  exact ih htail

/-- One target band assembled from restricted normalized route chunks. -/
structure BandCertificate (partials : List (List BetaFourRoutedContribution)) where
  lower : ℕ
  upper : ℕ
  bounds : lower ≤ upper
  pieces : List (Option (List BetaFourRoutedContribution))
  final : List BetaFourRoutedContribution
  restricted : List.Forall₂
    (fun source piece ↦ restrictSparse lower upper source = piece.getD []) partials pieces
  merged : MergeTrace [] (pieces.filterMap id) final
  canonical : IsCanonicalFrom lower upper final

namespace BandCertificate

/-- Inside its interval, a band certificate represents the pointwise sum of all partial rows. -/
theorem sparseNumeratorAt {partials : List (List BetaFourRoutedContribution)}
    (certificate : BandCertificate partials) (position : ℕ)
    (hlower : certificate.lower ≤ position) (hupper : position < certificate.upper) :
    BetaFourRoutedContribution.sparseNumeratorAt certificate.final position =
      (partials.map fun row ↦
        BetaFourRoutedContribution.sparseNumeratorAt row position).sum := by
  rw [certificate.merged.sparseNumeratorAt]
  simp only [BetaFourRoutedContribution.sparseNumeratorAt, Nat.zero_add]
  exact sum_sparseNumeratorAt_filterMap_eq_of_restricted_forall₂
    certificate.restricted hlower hupper

end BandCertificate

/-- Consecutive band certificates covering one half-open target interval. -/
inductive BandCover (partials : List (List BetaFourRoutedContribution)) :
    ℕ → ℕ → List (BandCertificate partials) → Prop
  | nil (start : ℕ) : BandCover partials start start []
  | cons {start limit : ℕ} (certificate : BandCertificate partials)
      (bands : List (BandCertificate partials))
      (hlower : certificate.lower = start)
      (tail : BandCover partials certificate.upper limit bands) :
      BandCover partials start limit (certificate :: bands)

/-- Canonical sparse row obtained by concatenating the final row of every target band. -/
def bandFinalRow {partials : List (List BetaFourRoutedContribution)}
    (bands : List (BandCertificate partials)) : List BetaFourRoutedContribution :=
  bands.flatMap (·.final)

namespace BandCover

/-- A consecutive band cover has ordered endpoints. -/
theorem start_le {partials : List (List BetaFourRoutedContribution)}
    {start limit : ℕ} {bands : List (BandCertificate partials)}
    (hcover : BandCover partials start limit bands) : start ≤ limit := by
  induction hcover with
  | nil => exact le_rfl
  | cons certificate bands hlower tail ih =>
      rw [← hlower]
      exact le_trans certificate.bounds ih

/-- Concatenating the rows of consecutive canonical bands is globally canonical. -/
theorem canonical {partials : List (List BetaFourRoutedContribution)}
    {start limit : ℕ} {bands : List (BandCertificate partials)}
    (hcover : BandCover partials start limit bands) :
    IsCanonicalFrom start limit (bandFinalRow bands) := by
  induction hcover with
  | nil => trivial
  | @cons start limit certificate bands hlower tail ih =>
      simp only [bandFinalRow, List.flatMap_cons]
      have hcertificate :
          IsCanonicalFrom start certificate.upper certificate.final := by
        rw [← hlower]
        exact certificate.canonical
      have hbounds : start ≤ certificate.upper := by
        rw [← hlower]
        exact certificate.bounds
      exact hcertificate.append ih hbounds tail.start_le

/-- At every covered position, the concatenated band row represents all normalized partials.

Proof sketch: exactly one consecutive band contains the requested position.  Its certificate gives
the desired sum; canonical range bounds make every preceding or following band evaluate to zero.
-/
theorem sparseNumeratorAt {partials : List (List BetaFourRoutedContribution)}
    {start limit : ℕ} {bands : List (BandCertificate partials)}
    (hcover : BandCover partials start limit bands) (position : ℕ)
    (hstart : start ≤ position) (hlimit : position < limit) :
    BetaFourRoutedContribution.sparseNumeratorAt (bandFinalRow bands) position =
      (partials.map fun row ↦
        BetaFourRoutedContribution.sparseNumeratorAt row position).sum := by
  induction hcover with
  | nil => omega
  | @cons start limit certificate bands hlower tail ih =>
      simp only [bandFinalRow, List.flatMap_cons,
        BetaFourRoutedContribution.sparseNumeratorAt_append]
      change BetaFourRoutedContribution.sparseNumeratorAt certificate.final position +
          BetaFourRoutedContribution.sparseNumeratorAt (bandFinalRow bands) position = _
      by_cases hband : position < certificate.upper
      · have hcertificateLower : certificate.lower ≤ position := by
          rw [hlower]
          exact hstart
        rw [certificate.sparseNumeratorAt position hcertificateLower hband]
        have htailCanonical := tail.canonical
        have hzero := htailCanonical.sparseNumeratorAt_eq_zero_of_lt_start hband
        rw [hzero, Nat.add_zero]
      · have hcertificateZero :
            BetaFourRoutedContribution.sparseNumeratorAt certificate.final position = 0 :=
          certificate.canonical.sparseNumeratorAt_eq_zero_of_limit_le
            (Nat.le_of_not_gt hband)
        rw [hcertificateZero, Nat.zero_add]
        exact ih (Nat.le_of_not_gt hband) hlimit

end BandCover

/-- A sharded certificate reconstructs the compact routed row and its true support bound.

The equality component is the arithmetic fact consumed downstream.  The second component records
that every source route targets the genuine unpadded support; it is intentionally carried beside
the numerical result so the sentinel check cannot become dead generated data.
-/
theorem dropZeros_scatterOn_range_eq_bandFinalRow_and_allTargetsBelow
    (rows : List (List (Option BetaFourRoutedContribution)))
    (chunks : List (List (List (Option BetaFourRoutedContribution))))
    (partials : List (List BetaFourRoutedContribution))
    (bands : List (BandCertificate partials))
    (width supportLength : ℕ)
    (hchunks : chunks.flatten = rows)
    (hnormalized : List.Forall₂
      (fun chunk normalized ↦ canonicalizeRows chunk = normalized) chunks partials)
    (hbounded : chunks.Forall fun chunk ↦ AllTargetsBelow supportLength chunk.flatten)
    (hcover : BandCover partials 0 width bands) :
    dropZeros (scatterOn rows.flatten (List.range width)) =
        (bandFinalRow bands).map (·.numerator) ∧
      AllTargetsBelow supportLength rows.flatten := by
  constructor
  · have hcanonical := hcover.canonical
    have hpointwise (position : ℕ) (hposition : position < width) :
        sparseNumeratorAt (bandFinalRow bands) position =
          numeratorAt rows.flatten position := by
      rw [hcover.sparseNumeratorAt position (by omega) hposition]
      rw [sum_sparseNumeratorAt_eq_numeratorAt_flatten_of_forall₂
        hnormalized position, hchunks]
    have hscatter :
        scatterOn rows.flatten (List.range width) =
          (List.range width).map (sparseNumeratorAt (bandFinalRow bands)) := by
      unfold scatterOn
      apply List.map_congr_left
      intro position hposition
      exact (hpointwise position (List.mem_range.mp hposition)).symm
    rw [hscatter, List.range_eq_range']
    rw [← expandSparseFrom_eq_map_range' 0 width (bandFinalRow bands)
      (by simpa using hcanonical)]
    exact dropZeros_expandSparseFrom 0 width (bandFinalRow bands) (by simpa using hcanonical)
  · rw [← hchunks]
    exact AllTargetsBelow.flatten₂_of_forall hbounded

/-!
## Dense target-band certificates

The sparse merge certificates above are useful when a downstream client needs the actual target
indices.  Numerical clients often need only the dense numerator row before zero deletion.  For
those clients, serializing every restricted sparse piece and every intermediate merge repeats the
same routed data many times.  `DenseBandCertificate` is the smaller alternative: after source
routes have been normalized once, it checks at most one bounded interval of output numerators.
-/

/-- A checked dense slice of the pointwise sum of normalized sparse route chunks.

The certificate stores the values on `[lower, upper)`. Generated clients should keep this interval
small (currently 64 positions). The theorem field is deliberately semantic: consumers use it
without unfolding the serialized values.
-/
structure DenseBandCertificate (partials : List (List BetaFourRoutedContribution)) where
  lower : ℕ
  upper : ℕ
  bounds : lower ≤ upper
  values : List ℕ
  values_eq :
    values = (List.range' lower (upper - lower)).map fun position ↦
      (partials.map fun row ↦ sparseNumeratorAt row position).sum

/-- Consecutive dense bands covering one half-open target interval. -/
inductive DenseBandCover (partials : List (List BetaFourRoutedContribution)) :
    ℕ → ℕ → List (DenseBandCertificate partials) → Prop
  | nil (start : ℕ) : DenseBandCover partials start start []
  | cons {start limit : ℕ} (certificate : DenseBandCertificate partials)
      (bands : List (DenseBandCertificate partials))
      (hlower : certificate.lower = start)
      (tail : DenseBandCover partials certificate.upper limit bands) :
      DenseBandCover partials start limit (certificate :: bands)

/-- Concatenate the checked dense values of a band family. -/
def denseBandValues {partials : List (List BetaFourRoutedContribution)}
    (bands : List (DenseBandCertificate partials)) : List ℕ :=
  bands.flatMap (·.values)

namespace DenseBandCover

/-- A consecutive dense-band cover has ordered endpoints. -/
theorem start_le {partials : List (List BetaFourRoutedContribution)}
    {start limit : ℕ} {bands : List (DenseBandCertificate partials)}
    (hcover : DenseBandCover partials start limit bands) : start ≤ limit := by
  induction hcover with
  | nil => exact le_rfl
  | cons certificate bands hlower tail ih =>
      rw [← hlower]
      exact le_trans certificate.bounds ih

/-- Concatenating consecutive dense bands gives the pointwise sum on the covered interval.

Proof sketch: each certificate identifies one `List.range'` slice. Consecutiveness makes adjacent
ranges append, and induction composes those slice equations without evaluating a larger band.
-/
theorem values_eq {partials : List (List BetaFourRoutedContribution)}
    {start limit : ℕ} {bands : List (DenseBandCertificate partials)}
    (hcover : DenseBandCover partials start limit bands) :
    denseBandValues bands =
      (List.range' start (limit - start)).map fun position ↦
        (partials.map fun row ↦ sparseNumeratorAt row position).sum := by
  induction hcover with
  | nil => simp [denseBandValues]
  | @cons start limit certificate bands hlower tail ih =>
      have hstartUpper : start ≤ certificate.upper := by
        rw [← hlower]
        exact certificate.bounds
      have hupperLimit : certificate.upper ≤ limit := tail.start_le
      change certificate.values ++ denseBandValues bands = _
      rw [certificate.values_eq, ih, hlower]
      rw [← List.map_append]
      have hstart : start + (certificate.upper - start) = certificate.upper := by omega
      have hlength :
          (certificate.upper - start) + (limit - certificate.upper) = limit - start := by
        omega
      have hrange := List.range'_append_1
        (s := start) (m := certificate.upper - start) (n := limit - certificate.upper)
      rw [hstart, hlength] at hrange
      exact congrArg
        (List.map fun position ↦
          (partials.map fun row ↦ sparseNumeratorAt row position).sum) hrange

end DenseBandCover

/-- Dense bands recover the routed output row while per-chunk checks retain sentinel safety.

This is the dense-band counterpart of
`dropZeros_scatterOn_range_eq_bandFinalRow_and_allTargetsBelow`. It never asks the kernel to
normalize the whole routed parent: each source chunk is normalized independently and each output
band supplies its own bounded value check.
-/
theorem dropZeros_scatterOn_range_eq_denseBandValues_and_allTargetsBelow
    (rows : List (List (Option BetaFourRoutedContribution)))
    (chunks : List (List (List (Option BetaFourRoutedContribution))))
    (partials : List (List BetaFourRoutedContribution))
    (bands : List (DenseBandCertificate partials))
    (width supportLength : ℕ)
    (hchunks : chunks.flatten = rows)
    (hnormalized : List.Forall₂
      (fun chunk normalized ↦ canonicalizeRows chunk = normalized) chunks partials)
    (hbounded : chunks.Forall fun chunk ↦ AllTargetsBelow supportLength chunk.flatten)
    (hcover : DenseBandCover partials 0 width bands) :
    dropZeros (scatterOn rows.flatten (List.range width)) =
        dropZeros (denseBandValues bands) ∧
      AllTargetsBelow supportLength rows.flatten := by
  constructor
  · rw [hcover.values_eq]
    simp only [Nat.sub_zero]
    rw [← List.range_eq_range']
    apply congrArg dropZeros
    unfold scatterOn
    apply List.map_congr_left
    intro position _
    rw [← hchunks]
    exact (sum_sparseNumeratorAt_eq_numeratorAt_flatten_of_forall₂
      hnormalized position).symm
  · rw [← hchunks]
    exact AllTargetsBelow.flatten₂_of_forall hbounded

end BetaFourRoutedContribution

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
