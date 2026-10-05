/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.CoarsenedSupportPreimage
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLocalizedStage
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalSelect

set_option autoImplicit false

/-!
# The reachable fine ambient, and `hfine` discharged

`Examples/DuanWuZhouLevelTwoPlainFineBridge.lean` refuted the old `dwz63PlainFine`: its support
kept an address only when all three coarse leg words pointed at the *same* retained triple, and a
legwise zero-out cannot impose that.  The repair is not to uncross downstream but to take the cut
the hash already made **upstream**, at the coarse level, and pull it back.

`dwz63PreimageFine` is the fine double power cut to the addresses whose *coarse image* is a
retained triple.  That is one condition per fine address, and it forces the three coarse leg words
to be the legs of one retained address --- because they are the legs of the coarse image, which is
that address.  Uncrossing is therefore free, and `hcover` holds by `Finset.mem_filter`.

`hfine` is then the composite of four committed steps: the power/positive-power bridge, the count
lane's hash restriction, the observation that a `withSupport` forgets the marginal `select`, and
`Restricts.coarsenedPositivePower_withSupport_to_preimage`.  No hypothesis survives.

`[DuanWuZhou2022]`, section 6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

noncomputable section

variable {R : Type v} [Field R]

/-- The fine double power of the section 6.3 partition. -/
noncomputable abbrev dwz63FineDoublePower (K : Type u) [CommRing K] (n : ℕ) :=
  ((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n

/-- **The reachable fine ambient**: the fine addresses whose coarse image is a retained triple. -/
noncomputable def dwz63PreimageFine (K : Type u) [CommRing K] (n : ℕ)
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) :=
  (dwz63FineDoublePower K n).withSupport
    (coarseningPreimageSupport (dwz63FineDoublePower K n)
      (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) retained)

@[simp] theorem mem_dwz63PreimageFine_support (K : Type u) [CommRing K] (n : ℕ)
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (s : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :
    s ∈ (dwz63PreimageFine K n retained).support ↔
      s ∈ (dwz63FineDoublePower K n).support ∧
        coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) s ∈ retained := by
  rw [dwz63PreimageFine, PartitionedTensor.withSupport_support,
    mem_coarseningPreimageSupport]

/-- **`hcover`, by construction.**  A supported address lies over its own coarse image, which is a
retained triple; there is nothing to uncross. -/
theorem dwz63PreimageFine_hcover (K : Type u) [CommRing K] (n : ℕ)
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) :
    ∀ s ∈ (dwz63PreimageFine K n retained).support, ∃ a : retained,
      ∀ c, (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c =
        positiveWordMap (cwSquareDegreeMap c) n (s c) := by
  intro s hs
  rw [mem_dwz63PreimageFine_support] at hs
  exact ⟨⟨_, hs.2⟩, fun _ ↦ rfl⟩

/-- **`hfine`, discharged.**  The plain power reaches the reachable fine ambient. -/
theorem dwz63_power_restricts_preimageFine [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (dwz63PreimageFine K n
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)).realize := by
  classical
  set retained := dwz63PlainJointRetainedSupport K hinj n t markedWords B seed with hret
  have hS : retained ⊆ ((dwz63FineDoublePower K n).coarsen
      (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n)).support := by
    intro a ha
    have h := dwz63_plainJointRetained_mem_positivePowerSupport K hinj n t markedWords B seed
      ⟨a, ha⟩
    rwa [Tensor.Restricts.positivePower_coarsen_support_eq
      ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n] at h
  have hforget :
      ((dwz63PlainMarginalTypicalPower K n t).withSupport retained).realize =
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
          cwSquareDegreeMap n).withSupport retained).realize := by
    refine PartitionedTensor.realize_eq_of_support_eq _ _ rfl ?_
    intro address _
    rfl
  refine ((Tensor.Restricts.power_partitionedPositivePower
    (cwSquarePartitionedTensor K dwz63Q) n).trans
    ((dwz63_restricts_positivePower_plainJointRetained K hinj n t markedWords hmarked B hB
      seed).trans (Restricts.of_eq hforget))).trans ?_
  exact Tensor.Restricts.coarsenedPositivePower_withSupport_to_preimage
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n retained hS

end

end AlgebraicComplexity.Examples
