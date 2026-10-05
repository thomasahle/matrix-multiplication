/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.TotalWeightAcceptanceAssembly
import AlgebraicComplexity.Tensor.CompatibilityIsolationCeiling

set_option autoImplicit false

/-!
# The outer `X`-word ceiling on the total-weight coarse power

`AlgebraicComplexity/Tensor/CompatibilityIsolationCeiling.lean` proves, uniformly in the
compatibility relation, that a sound compatibility zero-out on `pivot` retains only ambient
addresses whose `pivot` label no *other* ambient address uses.  This module instantiates that
ceiling at the ambient the outer total-weight cleanup actually names, and the result is that the
cleanup retains at most **one** address.

## What is proved

Let `P` be the total-weight-coarsened depth-`depth` CW chunk partition and
`cwTotalWeightCoarsePower K q depth n = P.positivePower n` its canonical `n+1`-letter power — the
literal ambient of `CWTotalWeightOuterCoarseCleanup.soundX`.  Two finite facts about that ambient
were missing from the tree; both are supplied here, generically in `depth`:

* **the coarse-power sum law** — a supported coarse letter has
  `wX + wY + wZ = coarseTotal depth` (`cwTotalWeightCoarseSupport_weight_sum`), and positionwise
  the same holds on the power (`cwTotalWeightCoarsePower_coarse_sum`).  This is the total-weight
  analogue of `cwSortedPairCoarseSupport_weight_sum`, which was committed only for the neighbouring
  sorted-pair coarsening at depth one;
* **realizability** — a supported CW letter whose `X` block is not `.last` admits a *second*
  `(Y, Z)` split (`cw002`/`cw011` above `X = .zero`, `cw101`/`cw110` above `X = .middle`), so a
  supported coarse letter with `X`-digit below `coarseTotal depth` has a different supported
  companion above the same `X`-digit (`exists_cwTotalWeightCoarseSupport_xEq_yNe`), hence so does a
  supported power address (`exists_cwTotalWeightCoarsePower_xEq_ne`).  Note that this needs no
  simplex-surjectivity statement: one alternate completion per light letter is enough, which is
  exactly the shape `Tensor.notMem_compatibilityIsolatedSupport_of_leg_eq` consumes.

Together they force every unique-`X`-fiber address of the full coarse power to be the single
address with `X`-word constantly `coarseTotal depth` and `Y`, `Z` words constantly `0`
(`cwTotalWeightCoarsePower_digit_of_mem_uniqueLegFiberSupport`), so

`card_uniqueLegFiberSupport_cwTotalWeightCoarsePower_le_one` and hence
`CWTotalWeightOuterCoarseCleanup.card_survivors_le_one`:
**every cleanup, every `r`, every `depth`, every `q`, and every compatibility relation retains at
most one survivor.**

Feeding that capacity `1` into the datum's own proved copy growth
(`CWTotalWeightLocalizedOuterSequenceData.outerBase_le_one_of_count_le_one`, which is
`Growth.le_of_pow_succ_le_subexponential_mul_pow_succ` at `ρ = 1`) forces `outerBase ≤ 1`, against
the `C′` copy base `2 ^ (38 · 811/125) = 2 ^ 246.544` that `OuterFloorInput.base` pins.  So
`OuterCountInput` is unsatisfiable — `false_of_outerCountInput`, `isEmpty_outerCountInput` — at
every depth, for every certificate, independently of the inner side.

## Scope — what this does *not* say

This is a statement about the **ambient of the isolation**, not about the flat depth-one frame.
The full write-up is `better_bound/flat_route_feasibility/CONSTRUCTION_SCOPE.md`; the three
conclusions this module is the Lean form of are:

* The forcing field is `CWTotalWeightOuterCoarseCleanup.soundX`, whose ambient is literally
  `(cwTotalWeightCoarsePower K q depth (n r)).support` — the **unrestricted** canonical power.  No
  choice of `compatibleX` escapes, because the ceiling does not mention the relation.  What is
  refuted is the record's ISOLATE-AGAINST-UNRESTRICTED shape, i.e. the mismatch between that
  ambient and the record's own docstring ("the survivors of the paper's `X` zero-out *after
  hashing*").
* A **hash-first** construction — restrict the support first, isolate against the restricted
  ambient, which is the paper's own order of operations and is already expressible in the committed
  hashing layer (`Tensor.Restricts.partitionedSelect`,
  `Tensor.Restricts.modeledTargets_to_hashFilteredPower` then `hashFilteredPower_to_xyIsolated`,
  `Examples/CoppersmithWinogradCompatibilityCoarseExtraction.lean`,
  `Tensor/GroupedCompatibilityZeroing.lean`) — does **not** face this ceiling.  It faces the
  *post-hash* `X`-word capacity instead: `TotalWeightAcceptanceCapacity.xWordCapacityBase`, whose
  depth-one value `5 ^ 152` is `4 log₂ 5 = 9.2877` bits per stride unit and therefore sits *above*
  the `C′` outer floor `6.488` (`outerBase_le_xWordCapacity_levelTwo`).  The two ceilings are
  different theorems about different objects and must not be conflated.
* Consequently nothing here licenses the phrase "structural obstruction to the flat frame".  The
  flat depth-one route is dormant-but-live; reviving it is a new outer interface (a cleanup record
  carrying a hashed sub-support, a coarse-alphabet field encoding and Salem--Spencer input, and an
  outer floor witness that pays the hash loss), not a repair of this record.

The depth-four capacity no-go `TotalWeightAcceptanceAssembly.false_of_named_outer_inputs` is a
*third*, logically independent argument (there the depth-four coarse-word alphabet `33 ^ 19` is
already too small); `isEmpty_levelFourOuterCountInput` below re-derives its conclusion from the
ceiling instead, without any depth-four arithmetic.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-! ## The coarse-power sum law -/

/-- The total coarse weight of a native CW chunk read off its `2 ^ depth` block letters. -/
theorem splitWordWeight_cwChunkSplitWord_eq_sum (depth : ℕ)
    (word : PositiveWord CWBlock (2 ^ depth - 1)) :
    splitWordWeight (cwChunkSplitWord depth word) =
      ∑ i, (cwBlockDigit (positiveWordEquiv CWBlock (2 ^ depth - 1) word i) : ℕ) := by
  unfold splitWordWeight
  exact Fintype.sum_equiv (cwChunkPositionEquiv depth).symm _ _ (fun _ ↦ rfl)

/-- Letterwise form of one total-weight coarse digit. -/
theorem cwTotalWeightChunkCoarsening_val_eq_sum (depth : ℕ) (c : Leg)
    (word : PositiveWord CWBlock (2 ^ depth - 1)) :
    (cwTotalWeightChunkCoarsening depth c word : ℕ) =
      ∑ i, (cwBlockDigit (positiveWordEquiv CWBlock (2 ^ depth - 1) word i) : ℕ) :=
  splitWordWeight_cwChunkSplitWord_eq_sum depth word

/-- **The sum law for the total-weight coarsening.**  A supported total-weight coarse letter obeys
the paper's equation `I + J + K = 2 ^ (depth + 1)`.

This is the total-weight analogue of `cwSortedPairCoarseSupport_weight_sum`, which the tree carried
only for the sorted-pair coarsening at depth one.  It is generic in `depth`. -/
theorem cwTotalWeightCoarseSupport_weight_sum
    (K : Type u) [CommRing K] (q depth : ℕ)
    (address : BlockAddress (fun _c : Leg ↦ CWCoarseDigit depth))
    (haddress : address ∈
      ((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).support) :
    (address .X : ℕ) + (address .Y : ℕ) + (address .Z : ℕ) = coarseTotal depth := by
  classical
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hmap⟩ := haddress
  have hmapAt (c : Leg) :
      cwTotalWeightChunkCoarsening depth c (fine c) = address c := by
    simpa [coarsenBlockAddress] using congrFun hmap c
  have hlegal := cwChunkPartitionedTensor_isEncodedFineLegalOnSupport K q depth fine hfine
  rw [← hmapAt .X, ← hmapAt .Y, ← hmapAt .Z]
  show splitWordWeight (cwChunkSplitWord depth (fine .X)) +
      splitWordWeight (cwChunkSplitWord depth (fine .Y)) +
      splitWordWeight (cwChunkSplitWord depth (fine .Z)) = coarseTotal depth
  unfold splitWordWeight coarseTotal
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    (∑ position,
        ((cwChunkSplitWord depth (fine .X) position : ℕ) +
          (cwChunkSplitWord depth (fine .Y) position : ℕ) +
          (cwChunkSplitWord depth (fine .Z) position : ℕ))) =
        ∑ _position : Fin (2 ^ depth), 2 :=
      Finset.sum_congr rfl (fun position _ ↦ hlegal position)
    _ = 2 ^ (depth + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Reading one leg of a transposed supported coarse word. -/
theorem cwTotalWeightCoarsePower_leg_apply
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (word : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) (c : Leg) :
    positiveWordEquiv (CWCoarseDigit depth) n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n word c) =
      fun sample ↦ (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n word sample).1 c :=
  positiveWordEquiv_positiveSupportWordBlockAddress
    (CWTotalWeightCoarseSupport K q depth) n word c

/-! ## Letterwise presentation of the two supports

Both supports involved are images of *words of supported letters*, so membership and legwise
reading are interchangeable with a plain function into the letter support.  These four lemmas are
the only place the transposition API is touched. -/

/-- Every word of supported CW block letters is realized by a supported chunk address. -/
theorem exists_cwChunkSupport_of_letters
    (K : Type u) [CommRing K] (q depth : ℕ)
    (letters : Fin (2 ^ depth - 1 + 1) → (cwPartitionedTensor K q).support) :
    ∃ fine ∈ (cwChunkPartitionedTensor K q depth).support,
      ∀ c : Leg,
        positiveWordEquiv CWBlock (2 ^ depth - 1) (fine c) = fun i ↦ (letters i).1 c := by
  classical
  refine ⟨positiveSupportWordBlockAddress (cwPartitionedTensor K q).support (2 ^ depth - 1)
    ((positiveWordEquiv (cwPartitionedTensor K q).support (2 ^ depth - 1)).symm letters),
    ?_, fun c ↦ ?_⟩
  · show _ ∈ ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).support
    rw [(cwPartitionedTensor K q).positivePower_support_eq_image_positiveSupportWordBlockAddress]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · rw [positiveWordEquiv_positiveSupportWordBlockAddress
      (cwPartitionedTensor K q).support (2 ^ depth - 1)
      ((positiveWordEquiv (cwPartitionedTensor K q).support (2 ^ depth - 1)).symm letters) c,
      Equiv.apply_symm_apply]

/-- Conversely, every supported chunk address is a word of supported CW block letters. -/
theorem exists_letters_of_mem_cwChunkSupport
    (K : Type u) [CommRing K] (q depth : ℕ)
    {fine : BlockAddress (fun _c : Leg ↦ PositiveWord CWBlock (2 ^ depth - 1))}
    (hfine : fine ∈ (cwChunkPartitionedTensor K q depth).support) :
    ∃ letters : Fin (2 ^ depth - 1 + 1) → (cwPartitionedTensor K q).support,
      ∀ c : Leg,
        positiveWordEquiv CWBlock (2 ^ depth - 1) (fine c) = fun i ↦ (letters i).1 c := by
  classical
  have hfineMem : fine ∈ ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).support := hfine
  obtain ⟨source, hsource⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support
      (2 ^ depth - 1) hfineMem
  refine ⟨positiveWordEquiv (cwPartitionedTensor K q).support (2 ^ depth - 1) source, fun c ↦ ?_⟩
  rw [← hsource]
  exact positiveWordEquiv_positiveSupportWordBlockAddress
    (cwPartitionedTensor K q).support (2 ^ depth - 1) source c

/-- Every word of supported coarse chunk letters is realized by a supported coarse power address. -/
theorem exists_cwTotalWeightCoarsePower_of_chunks
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (chunks : Fin (n + 1) → CWTotalWeightCoarseSupport K q depth) :
    ∃ address ∈ (cwTotalWeightCoarsePower K q depth n).support,
      ∀ c : Leg,
        positiveWordEquiv (CWCoarseDigit depth) n (address c) = fun t ↦ (chunks t).1 c := by
  classical
  refine ⟨positiveSupportWordBlockAddress (CWTotalWeightCoarseSupport K q depth) n
    ((positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n).symm chunks), ?_, fun c ↦ ?_⟩
  · rw [PartitionedTensor.positivePower_support_eq_image_positiveSupportWordBlockAddress]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · rw [cwTotalWeightCoarsePower_leg_apply K q depth n
      ((positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n).symm chunks) c,
      Equiv.apply_symm_apply]

/-- Conversely, every supported coarse power address is a word of supported coarse chunk letters. -/
theorem exists_chunks_of_mem_cwTotalWeightCoarsePower
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {address : BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n)}
    (haddress : address ∈ (cwTotalWeightCoarsePower K q depth n).support) :
    ∃ chunks : Fin (n + 1) → CWTotalWeightCoarseSupport K q depth,
      ∀ c : Leg,
        positiveWordEquiv (CWCoarseDigit depth) n (address c) = fun t ↦ (chunks t).1 c := by
  classical
  obtain ⟨word, hword⟩ :=
    ((cwChunkPartitionedTensor K q depth).coarsen
      (cwTotalWeightChunkCoarsening depth)).exists_positiveSupportWord_of_mem_positivePower_support
        n haddress
  refine ⟨positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n word, fun c ↦ ?_⟩
  rw [← hword]
  exact cwTotalWeightCoarsePower_leg_apply K q depth n word c

/-- The sum law on the coarse power: every sample of a supported address obeys the coordinatewise
equation. -/
theorem cwTotalWeightCoarsePower_coarse_sum
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (address : BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈ (cwTotalWeightCoarsePower K q depth n).support)
    (sample : Fin (n + 1)) :
    (positiveWordEquiv (CWCoarseDigit depth) n (address .X) sample : ℕ) +
        (positiveWordEquiv (CWCoarseDigit depth) n (address .Y) sample : ℕ) +
        (positiveWordEquiv (CWCoarseDigit depth) n (address .Z) sample : ℕ) =
      coarseTotal depth := by
  classical
  obtain ⟨chunks, hchunks⟩ :=
    exists_chunks_of_mem_cwTotalWeightCoarsePower K q depth n haddress
  rw [hchunks .X, hchunks .Y, hchunks .Z]
  exact cwTotalWeightCoarseSupport_weight_sum K q depth
    (chunks sample).1 (chunks sample).2

/-! ## Realizability: a light `X` letter admits a second `(Y, Z)` split -/

/-- **The realizability witness.**  Above every CW `X` block other than `.last` the six-address
support carries two different `(Y, Z)` splits: `cw002`/`cw011`/`cw020` above `X = .zero` and
`cw101`/`cw110` above `X = .middle`.

This is all the realizability the ceiling needs; in particular no surjectivity onto the coarse
simplex is asserted. -/
theorem exists_cwBlockSupport_xEq_yNe
    (block : CWBlockAddress) (hblock : block ∈ cwBlockSupport)
    (hx : block .X ≠ CWBlock.last) :
    ∃ other ∈ cwBlockSupport, other .X = block .X ∧ other .Y ≠ block .Y := by
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hblock
  rcases hblock with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (by decide) hx
  · exact ⟨cw002, by decide, by decide, by decide⟩
  · exact ⟨cw020, by decide, by decide, by decide⟩
  · exact ⟨cw002, by decide, by decide, by decide⟩
  · exact ⟨cw110, by decide, by decide, by decide⟩
  · exact ⟨cw101, by decide, by decide, by decide⟩

/-- **Realizability at the coarse chunk alphabet.**  A supported total-weight coarse letter whose
`X` digit is *below* `coarseTotal depth` has a different supported coarse letter above the same `X`
digit.

Proof: the `X` digit is the sum of the `2 ^ depth` block `X` digits, so a digit below
`coarseTotal depth = 2 · 2 ^ depth` forces some block letter to have `X` block other than `.last`;
`exists_cwBlockSupport_xEq_yNe` replaces that one letter, which preserves the whole `X` split word
and changes the `Y` weight by a nonzero amount. -/
theorem exists_cwTotalWeightCoarseSupport_xEq_yNe
    (K : Type u) [CommRing K] (q depth : ℕ)
    (address : BlockAddress (fun _c : Leg ↦ CWCoarseDigit depth))
    (haddress : address ∈
      ((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).support)
    (hx : (address .X : ℕ) < coarseTotal depth) :
    ∃ other ∈ ((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).support,
      other .X = address .X ∧ other .Y ≠ address .Y := by
  classical
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hmap⟩ := haddress
  obtain ⟨letters, hletters⟩ := exists_letters_of_mem_cwChunkSupport K q depth hfine
  have hdigit (c : Leg) :
      (address c : ℕ) = ∑ i, (cwBlockDigit ((letters i).1 c) : ℕ) := by
    have hmapAt : cwTotalWeightChunkCoarsening depth c (fine c) = address c := by
      simpa [coarsenBlockAddress] using congrFun hmap c
    rw [← hmapAt, cwTotalWeightChunkCoarsening_val_eq_sum, hletters c]
  -- Some block letter is not the `X` corner.
  have hlight : ∃ i, (letters i).1 .X ≠ CWBlock.last := by
    by_contra hnone
    have hall : ∀ i, (letters i).1 .X = CWBlock.last := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    have hfull : (address .X : ℕ) = coarseTotal depth := by
      rw [hdigit .X]
      calc
        (∑ i, (cwBlockDigit ((letters i).1 .X) : ℕ)) =
            ∑ _i : Fin (2 ^ depth - 1 + 1), 2 :=
          Finset.sum_congr rfl (fun i _ ↦ by rw [hall i]; rfl)
        _ = coarseTotal depth := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            two_pow_sub_one_add_one]
          simp [coarseTotal, pow_succ, Nat.mul_comm]
    omega
  obtain ⟨position, hposition⟩ := hlight
  have hpositionMem : (letters position).1 ∈ cwBlockSupport := (letters position).2
  obtain ⟨alternate, halternateMem, halternateX, halternateY⟩ :=
    exists_cwBlockSupport_xEq_yNe (letters position).1 hpositionMem hposition
  have halternateMem' : alternate ∈ (cwPartitionedTensor K q).support := halternateMem
  obtain ⟨letters', hAt, hOff⟩ :
      ∃ f : Fin (2 ^ depth - 1 + 1) → (cwPartitionedTensor K q).support,
        f position = ⟨alternate, halternateMem'⟩ ∧ ∀ i, i ≠ position → f i = letters i :=
    ⟨fun i ↦ if i = position then ⟨alternate, halternateMem'⟩ else letters i,
      if_pos rfl, fun i hi ↦ if_neg hi⟩
  obtain ⟨fine', hfine'Mem, hletters'⟩ := exists_cwChunkSupport_of_letters K q depth letters'
  have hdigit' (c : Leg) :
      ((coarsenBlockAddress (cwTotalWeightChunkCoarsening depth) fine') c : ℕ) =
        ∑ i, (cwBlockDigit ((letters' i).1 c) : ℕ) := by
    show (cwTotalWeightChunkCoarsening depth c (fine' c) : ℕ) = _
    rw [cwTotalWeightChunkCoarsening_val_eq_sum, hletters' c]
  refine ⟨coarsenBlockAddress (cwTotalWeightChunkCoarsening depth) fine', ?_, ?_, ?_⟩
  · rw [PartitionedTensor.coarsen_support]
    exact Finset.mem_image.mpr ⟨fine', hfine'Mem, rfl⟩
  · apply Fin.ext
    rw [hdigit' .X, hdigit .X]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    by_cases hi : i = position
    · subst hi
      simp [hAt, halternateX]
    · rw [hOff i hi]
  · intro hcontra
    have hvals : (∑ i, (cwBlockDigit ((letters' i).1 .Y) : ℕ)) =
        ∑ i, (cwBlockDigit ((letters i).1 .Y) : ℕ) := by
      rw [← hdigit' .Y, ← hdigit .Y, hcontra]
    have herase : (∑ i ∈ Finset.univ.erase position,
          (cwBlockDigit ((letters' i).1 .Y) : ℕ)) =
        ∑ i ∈ Finset.univ.erase position, (cwBlockDigit ((letters i).1 .Y) : ℕ) :=
      Finset.sum_congr rfl
        (fun i hi ↦ by rw [hOff i (Finset.ne_of_mem_erase hi)])
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ position),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ position)] at hvals
    have hlast : (cwBlockDigit ((letters' position).1 .Y) : ℕ) =
        (cwBlockDigit ((letters position).1 .Y) : ℕ) := by omega
    rw [hAt] at hlast
    exact halternateY (cwBlockDigit_injective (Fin.ext hlast))

/-- **Realizability on the coarse power.**  A supported coarse power address with an `X` digit
below `coarseTotal depth` at some sample has a *different* supported address with the *same* `X`
word.  This is exactly the input of `Tensor.notMem_compatibilityIsolatedSupport_of_leg_eq`. -/
theorem exists_cwTotalWeightCoarsePower_xEq_ne
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (address : BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈ (cwTotalWeightCoarsePower K q depth n).support)
    (sample : Fin (n + 1))
    (hx : (positiveWordEquiv (CWCoarseDigit depth) n (address .X) sample : ℕ) <
      coarseTotal depth) :
    ∃ other ∈ (cwTotalWeightCoarsePower K q depth n).support,
      other .X = address .X ∧ other ≠ address := by
  classical
  obtain ⟨chunks, hchunks⟩ :=
    exists_chunks_of_mem_cwTotalWeightCoarsePower K q depth n haddress
  have hxdigit : ((chunks sample).1 .X : ℕ) < coarseTotal depth := by
    rw [hchunks .X] at hx
    exact hx
  obtain ⟨alternate, halternateMem, halternateX, halternateY⟩ :=
    exists_cwTotalWeightCoarseSupport_xEq_yNe K q depth (chunks sample).1
      (chunks sample).2 hxdigit
  obtain ⟨chunks', hAt, hOff⟩ :
      ∃ f : Fin (n + 1) → CWTotalWeightCoarseSupport K q depth,
        f sample = ⟨alternate, halternateMem⟩ ∧ ∀ t, t ≠ sample → f t = chunks t :=
    ⟨fun t ↦ if t = sample then ⟨alternate, halternateMem⟩ else chunks t,
      if_pos rfl, fun t ht ↦ if_neg ht⟩
  obtain ⟨other, hotherMem, hchunks'⟩ :=
    exists_cwTotalWeightCoarsePower_of_chunks K q depth n chunks'
  refine ⟨other, hotherMem, ?_, ?_⟩
  · apply (positiveWordEquiv (CWCoarseDigit depth) n).injective
    rw [hchunks' .X, hchunks .X]
    funext t
    by_cases ht : t = sample
    · subst ht
      rw [hAt]
      exact halternateX
    · rw [hOff t ht]
  · intro hcontra
    have hleg : (fun t ↦ (chunks' t).1 .Y) = fun t ↦ (chunks t).1 .Y := by
      rw [← hchunks' .Y, ← hchunks .Y, hcontra]
    have hat := congrFun hleg sample
    rw [hAt] at hat
    exact halternateY hat

/-! ## The ceiling: at most one survivor -/

/-- The only coarse digit profile a unique-`X`-fiber address of the full coarse power can have:
everything on `X`. -/
def cwUniqueXFiberDigit (depth : ℕ) : Leg → ℕ
  | .X => coarseTotal depth
  | .Y => 0
  | .Z => 0

/-- **The ceiling, pointwise.**  Every address of the full total-weight coarse power whose `X` word
no other supported address uses has `X` word constantly `coarseTotal depth` and `Y`, `Z` words
constantly `0`. -/
theorem cwTotalWeightCoarsePower_digit_of_mem_uniqueLegFiberSupport
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (address : BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      uniqueLegFiberSupport (cwTotalWeightCoarsePower K q depth n).support .X)
    (c : Leg) (sample : Fin (n + 1)) :
    (positiveWordEquiv (CWCoarseDigit depth) n (address c) sample : ℕ) =
      cwUniqueXFiberDigit depth c := by
  classical
  obtain ⟨hmem, hunique⟩ :=
    (mem_uniqueLegFiberSupport (cwTotalWeightCoarsePower K q depth n).support .X address).mp
      haddress
  have hX : (positiveWordEquiv (CWCoarseDigit depth) n (address .X) sample : ℕ) =
      coarseTotal depth := by
    by_contra hne
    have hlt : (positiveWordEquiv (CWCoarseDigit depth) n (address .X) sample : ℕ) <
        coarseTotal depth := by
      have hbound :=
        (positiveWordEquiv (CWCoarseDigit depth) n (address .X) sample).isLt
      simp only [coarseTotal] at hne ⊢
      omega
    obtain ⟨other, hotherMem, hotherX, hotherNe⟩ :=
      exists_cwTotalWeightCoarsePower_xEq_ne K q depth n address hmem sample hlt
    exact hotherNe (hunique other hotherMem hotherX)
  have hsum := cwTotalWeightCoarsePower_coarse_sum K q depth n address hmem sample
  cases c with
  | X => exact hX
  | Y => simp only [cwUniqueXFiberDigit]; omega
  | Z => simp only [cwUniqueXFiberDigit]; omega

/-- **The ceiling, counting form.**  The full total-weight coarse power has at most one address
whose `X` word is its own.  Hence no compatibility zero-out on `.X` against that ambient can retain
more than one address, whatever the relation. -/
theorem card_uniqueLegFiberSupport_cwTotalWeightCoarsePower_le_one
    (K : Type u) [CommRing K] (q depth n : ℕ) :
    (uniqueLegFiberSupport
      (cwTotalWeightCoarsePower K q depth n).support .X).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro left hleft right hright
  funext c
  apply (positiveWordEquiv (CWCoarseDigit depth) n).injective
  funext sample
  apply Fin.ext
  rw [cwTotalWeightCoarsePower_digit_of_mem_uniqueLegFiberSupport K q depth n left hleft c sample,
    cwTotalWeightCoarsePower_digit_of_mem_uniqueLegFiberSupport K q depth n right hright c sample]

namespace CWTotalWeightOuterCoarseCleanup

variable {K : Type u} [CommRing K] {q depth : ℕ} {n : ℕ → ℕ}

/-- The survivors of the outer cleanup sit inside the ambient's singleton-`X`-fiber set.  This is
`Tensor.compatibilityIsolatedSupport_subset_uniqueLegFiberSupport` applied to `soundX`, which is
uniform in `compatibleX`. -/
theorem survivors_subset_uniqueLegFiberSupport
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (r : ℕ) :
    data.survivors r ⊆
      uniqueLegFiberSupport (cwTotalWeightCoarsePower K q depth (n r)).support .X :=
  (((compatibilityIsolatedSupport_subset _ _ _).trans
      (compatibilityIsolatedSupport_subset _ _ _)) :
        data.survivors r ⊆ data.xSupport r).trans
    (compatibilityIsolatedSupport_subset_uniqueLegFiberSupport
      (cwTotalWeightCoarsePower K q depth (n r)).support .X (data.compatibleX r)
      (data.soundX r))

/-- **The kill.**  Every outer total-weight coarse cleanup retains at most one survivor — at every
level `r`, at every recursion `depth`, for every `q`, and for every choice of the three
compatibility relations.

The bound is a property of the *ambient* named by `soundX`, the unrestricted coarse power, and no
choice of `compatibleX` can improve it. -/
theorem card_survivors_le_one
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (r : ℕ) :
    (data.survivors r).card ≤ 1 :=
  le_trans (Finset.card_le_card (data.survivors_subset_uniqueLegFiberSupport r))
    (card_uniqueLegFiberSupport_cwTotalWeightCoarsePower_le_one K q depth (n r))

end CWTotalWeightOuterCoarseCleanup

namespace CWTotalWeightLocalizedOuterSequenceData

/-- A localized outer total-weight sequence whose survivor count never exceeds one has copy base at
most one.  This is the datum's own proved `copy_growth` against
`Growth.le_of_pow_succ_le_subexponential_mul_pow_succ` at capacity `1`. -/
theorem outerBase_le_one_of_count_le_one
    {K : Type u} [CommRing K] {q depth : ℕ}
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {stride : ℕ} {outerBase : ℝ}
    (data : CWTotalWeightLocalizedOuterSequenceData.{u, v, w} K q depth T stride outerBase)
    (hcount : ∀ r, 0 < r → data.count r ≤ 1) :
    outerBase ≤ 1 := by
  refine Growth.le_of_pow_succ_le_subexponential_mul_pow_succ (ρ := 1)
    (loss := data.loss) zero_le_one data.loss_subexponential ?_
  intro m
  have hpos : 0 < m + 1 := Nat.succ_pos m
  refine (data.copy_growth (m + 1) hpos).trans ?_
  rw [one_pow, mul_one]
  have hle : ((data.count (m + 1) : ℝ)) ≤ 1 := by
    exact_mod_cast hcount (m + 1) hpos
  calc
    data.loss (m + 1) * (data.count (m + 1) : ℝ) ≤ data.loss (m + 1) * 1 :=
      mul_le_mul_of_nonneg_left hle (le_of_lt (data.loss_pos (m + 1) hpos))
    _ = data.loss (m + 1) := mul_one _

end CWTotalWeightLocalizedOuterSequenceData

end AlgebraicComplexity.Examples

namespace MatrixMultiplication.TotalWeightAcceptanceAssembly

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.TotalWeightAcceptanceFloors

universe u

/-- The `C′` outer copy base `2 ^ (38 · 811/125) = 2 ^ 246.544` exceeds one. -/
theorem one_lt_outerFloorCopyBase :
    (1 : ℝ) < (2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetainedFloor) := by
  have hexponent : (0 : ℝ) < ((38 : ℕ) : ℝ) * outerRetainedFloor := by
    norm_num [outerRetainedFloor]
  exact (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, hexponent⟩)

/-- **`h3` is unsatisfiable.**  The residual outer-count record of the total-weight acceptance
assembly has no instance at any depth, for any chunk alignment, and independently of the inner
side.

The ceiling forces `(cleanup.survivors r).card ≤ 1`; the record's own `count_pos`, `targetGrowth`
and `fullBucket` fields build a sequence datum whose proved copy growth then forces
`2 ^ (38 · 811/125) ≤ 1`. -/
theorem false_of_outerCountInput
    (K : Type u) [CommRing K] (q depth e stride : ℕ) (hstride : 0 < stride)
    {n : ℕ → ℕ}
    (halign : ∀ r, 0 < r → e * (stride * r) = 2 ^ depth * (n r + 1))
    {Part : Type} [Fintype Part]
    (floor : OuterFloorInput depth)
    (coarseRef : ∀ r, PositiveWord (CWTotalWeightCoarseSupport K q depth) (n r))
    (h3 : OuterCountInput K q depth n Part floor coarseRef) :
    False := by
  classical
  set data := CWTotalWeightLocalizedOuterSequenceData.ofChunkAlignedCoarseCleanup
    K q depth e stride floor.targetBase floor.xFieldBase
    ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetainedFloor))
    hstride floor.targetBase_pos floor.xFieldBase_nonneg
    floor.ySourceProfile floor.zSourceProfile
    floor.yJointExponentPerRepetition floor.zJointExponentPerRepetition
    floor.base h3.characteristicFloor h3.targetLoss h3.xFieldLoss h3.targetCount
    h3.xRequirement h3.visibleRequirement n (fun _ _ _ ↦ 0) h3.cleanup halign
    h3.targetLoss_subexponential h3.xFieldLoss_subexponential
    h3.targetLoss_pos h3.xFieldLoss_pos h3.count_pos h3.targetGrowth
    h3.xRequirement_le h3.visibleRequirement_le h3.fullBucket with hdata
  have hspec := CWTotalWeightLocalizedOuterSequenceData.ofChunkAlignedCoarseCleanup_spec
    K q depth e stride floor.targetBase floor.xFieldBase
    ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetainedFloor))
    hstride floor.targetBase_pos floor.xFieldBase_nonneg
    floor.ySourceProfile floor.zSourceProfile
    floor.yJointExponentPerRepetition floor.zJointExponentPerRepetition
    floor.base h3.characteristicFloor h3.targetLoss h3.xFieldLoss h3.targetCount
    h3.xRequirement h3.visibleRequirement n (fun _ _ _ ↦ 0) h3.cleanup halign
    h3.targetLoss_subexponential h3.xFieldLoss_subexponential
    h3.targetLoss_pos h3.xFieldLoss_pos h3.count_pos h3.targetGrowth
    h3.xRequirement_le h3.visibleRequirement_le h3.fullBucket hdata
  have hbase := data.outerBase_le_one_of_count_le_one (fun r _ ↦ by
    rw [hspec.2.2.1 r]
    exact h3.cleanup.card_survivors_le_one r)
  exact absurd hbase (not_le_of_gt one_lt_outerFloorCopyBase)

/-- `IsEmpty` form of `false_of_outerCountInput`. -/
theorem isEmpty_outerCountInput
    (K : Type u) [CommRing K] (q depth e stride : ℕ) (hstride : 0 < stride)
    {n : ℕ → ℕ}
    (halign : ∀ r, 0 < r → e * (stride * r) = 2 ^ depth * (n r + 1))
    {Part : Type} [Fintype Part]
    (floor : OuterFloorInput depth)
    (coarseRef : ∀ r, PositiveWord (CWTotalWeightCoarseSupport K q depth) (n r)) :
    IsEmpty (OuterCountInput K q depth n Part floor coarseRef) :=
  ⟨fun h3 ↦ false_of_outerCountInput K q depth e stride hstride halign floor coarseRef h3⟩

/-- The depth-one (paper level-two) instance: `8 · 38 · r = 2 · (152 · r)`, so the outer exponent is
`152 · r − 1`.  This is `TotalWeightAcceptanceAssemblyLevelTwo.levelTwoOuterExponent`, spelled out
so this module stays independent of that dormant assembly. -/
theorem isEmpty_levelTwoOuterCountInput
    (K : Type u) [CommRing K] {Part : Type} [Fintype Part]
    (floor : OuterFloorInput 1)
    (coarseRef : ∀ r, PositiveWord (CWTotalWeightCoarseSupport K 5 1) (152 * r - 1)) :
    IsEmpty (OuterCountInput K 5 1 (fun r ↦ 152 * r - 1) Part floor coarseRef) :=
  isEmpty_outerCountInput K 5 1 8 38 (by norm_num)
    (fun r _hr ↦ by
      show 8 * (38 * r) = 2 ^ 1 * (152 * r - 1 + 1)
      omega) floor coarseRef

/-- The depth-four instance, i.e. an obstruction to the `2.36999` outer record of
`TotalWeightAcceptanceAssembly` that is independent of the coarse-word capacity argument of
`TotalWeightAcceptanceNoGo`. -/
theorem isEmpty_levelFourOuterCountInput
    (K : Type u) [CommRing K] {Part : Type} [Fintype Part]
    (floor : OuterFloorInput 4)
    (coarseRef : ∀ r, PositiveWord (CWTotalWeightCoarseSupport K 5 4)
      (CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent r)) :
    IsEmpty (OuterCountInput K 5 4
      CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent Part floor coarseRef) :=
  isEmpty_outerCountInput K 5 4 8 38 (by norm_num)
    (fun r hr ↦ CWTotalWeightLocalizedOuterSequenceData.levelFour_align r hr) floor coarseRef

end MatrixMultiplication.TotalWeightAcceptanceAssembly
