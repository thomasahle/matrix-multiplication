/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingPower
import AlgebraicComplexity.Tensor.SingleLegHoleRepair
import AlgebraicComplexity.Combinatorics.ShufflingGroup

/-!
# The shuffling group of a restricted-splitting power, and its Hole Lemma

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module proves the two tensor claims
that `[DuanWuZhou2022]` make about the shuffling group, and assembles them with the layer-1 repair
(`Tensor/SingleLegHoleRepair.lean`) and the layer-2 union bound
(`Combinatorics/ShufflingGroup.lean`) into the Hole Lemma for restricted-splitting powers.

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§5 (`hole_lemma.tex`)** (`[DuanWuZhou2022]`).

## The paper's two claims

Fix a level-`ℓ` component and its restricted-splitting power `T^{⊗n}[α̃]`
(`MatrixMultiplication/RestrictedSplittingPower.lean`).  `[DuanWuZhou2022]` let the shuffling group
permute word positions and assert:

* **Claim 1** (`hole_lemma.tex` l.95, proved in the source): a small Z-block is available if and
  only if its image is.  Here this is `SplitRestriction.keeps_positionEquiv`: availability is the
  empirical type of the block word, and the empirical type is invariant under reindexing of
  positions (`WordType.multiplicity_reindex`).
* **Claim 2** (`hole_lemma.tex` l.105, **stated with no proof in the source** — the entire
  justification is the sentence "we keep the relative arrangement of variables within each block
  unchanged").  Here this is `PartitionedTensor.restrictedSplittingShuffle`: the position shuffle
  lifts to a genuine `StructureRelabeling` of `T^{⊗n}[α̃]`, i.e. a legwise permutation of block
  labels *together with* linear identifications of every dependent block space, satisfying
  `reindex = id` on the nose.

## Status of Claim 2 — resolution of watchlist item 8

**Proved as stated, with one hypothesis the paper does not make explicit.**  The paper's φ is a
permutation of positions of the *whole* standard form tensor which must act *by the same
permutation on all three legs*.  Nothing in the paper's prose says so — it defines φ separately on
X-, Y- and Z-blocks by "reordering the entries" — but the claim is false without it: three
unrelated position permutations do not preserve the term set of a tensor power, since a term of
`T^{⊗n}` couples the X-, Y- and Z-letters occurring at the *same* position.  The formalization
therefore takes a single `σ : Equiv.Perm (Fin (n+1))` and applies it on every leg, which is what
`Tensor/PartitionedPowerRelabeling.lean` already supplies; the same requirement is recorded there
("the same permutation acts on all three legs ... is exactly what distinguishes a legitimate
reordering of tensor factors from three unrelated permutations of the block words").  This is
recorded as source-correction item 17 in `better_bound/DWZ_SCOPING.md`.

Given that reading, the variable-level statement is *not* an extra obligation on top of the
block-level one: the variable-level identifications are the `blockEquiv` field of the
`StructureRelabeling`, and they are produced by the symmetric-monoidal coherence of external
products.  The remaining work is exactly the descent from the ambient power to the restricted
power, which is `StructureRelabeling.select` applied to Claim 1.

## Principal results

* `SplitRestriction.keeps_positionEquiv` — Claim 1 (availability is shuffle-invariant).
* `PartitionedTensor.restrictedSplittingShuffle` — Claim 2 (the shuffle is an automorphism of
  `T^{⊗n}[α̃]`), with `mem_restrictedSplittingPower_support_shuffle` recording that it permutes
  the available block addresses.
* `AvailableWord`, `availableWordShuffle`, `uniformOnAvailableWords` — the available small blocks
  on the restricted leg, the shuffling action on them, and **Claim 3**: that action is uniform, so
  a random shuffle sends a fixed available block to a uniformly random available block.
* `Tensor.Restricts.indexedDirectSum_restrictedSplittingHoleRepair` — **the Hole Lemma**: broken
  copies of `T^{⊗n}[α̃]` whose hole sets satisfy `|avail| · ∏_t |H_t| < |avail|^s` degenerate to
  one intact copy.

## Non-goals

The passage from the paper's hypothesis `∑_t η_t ≥ Nℓ + 1` to the finite inequality above is the
estimate `∏_t (1 − η_t) ≤ e^{−∑_t η_t}` together with the block count `|avail| ≤ 2^{Nℓ}`.  Both are
client-side facts about a concrete component (only there is `|avail|` known), and the corollary
`s' = ⌊∑ η/(Nℓ+2)⌋` is a grouping argument on top of them; neither is repeated here.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-! ## Claim 1: availability is invariant under position shuffling -/

/-- The empirical type of a block word is unchanged by a permutation of word positions. -/
theorem multiplicity_positiveWordPositionEquiv (I : Type w) [Fintype I] (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (word : PositiveWord I n) :
    WordType.multiplicity (positiveWordEquiv I n (positiveWordPositionEquiv I n σ word)) =
      WordType.multiplicity (positiveWordEquiv I n word) := by
  rw [positiveWordEquiv_position_apply]
  have h := WordType.multiplicity_reindex (α := I) σ.symm (positiveWordEquiv I n word)
  rw [Equiv.symm_symm] at h
  exact h

omit [∀ c, DecidableEq (A c)] in
/-- **`[DuanWuZhou2022]`, `hole_lemma.tex` Claim 1.**  A block word survives the split restriction
if and only if its position shuffle does; equivalently, the shuffling group permutes the
*available* small blocks. -/
theorem SplitRestriction.keeps_positionEquiv (profile : SplitRestriction A) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (c : Leg) (word : PositiveWord (A c) n) :
    profile.Keeps n c (positiveWordPositionEquiv (A c) n σ word) ↔ profile.Keeps n c word := by
  rcases hprofile : profile c with _ | α
  · simp [SplitRestriction.Keeps, hprofile]
  · rw [SplitRestriction.keeps_some_iff hprofile, SplitRestriction.keeps_some_iff hprofile,
      multiplicity_positiveWordPositionEquiv]

omit [∀ c, DecidableEq (A c)] in
/-- The inverse form of Claim 1, which is the shape required by
`PartitionedTensor.StructureRelabeling.select`. -/
theorem SplitRestriction.keeps_positionEquiv_symm (profile : SplitRestriction A) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (c : Leg) (word : PositiveWord (A c) n) :
    profile.Keeps n c ((positiveWordPositionEquiv (A c) n σ).symm word) ↔
      profile.Keeps n c word := by
  rw [positiveWordPositionEquiv_symm]
  exact SplitRestriction.keeps_positionEquiv profile n σ.symm c word

/-! ## Claim 2: the shuffle is an automorphism of the restricted power -/

namespace Tensor.PartitionedTensor

/-- **`[DuanWuZhou2022]`, `hole_lemma.tex` Claim 2 — the automorphism claim.**

A permutation `σ` of word positions, applied simultaneously on all three legs, is a
structure-preserving relabeling of the restricted-splitting power `T^{⊗(n+1)}[α̃]`: it permutes the
block labels, carries every dependent block space isomorphically to the block space at the moved
label, and leaves the partitioned tensor invariant on the nose.

The source states this with no proof.  See the module doc for the hypothesis it omits: the same
`σ` must act on all three legs.

Proof sketch: the ambient power already has such a relabeling
(`StructureRelabeling.positivePowerPositionRelabeling`, built from the symmetric monoidal
coherence of external products, which is where the variable-level identifications come from).  A
relabeling descends to a selection whose keep predicate it preserves
(`StructureRelabeling.select`), and the keep predicate here is availability, preserved by Claim
1. -/
noncomputable def restrictedSplittingShuffle
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) (profile : SplitRestriction A)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (P.restrictedSplittingPower n profile).StructureRelabeling :=
  (PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling P n σ).select
    (profile.Keeps n) fun c word ↦ by
      rw [PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv]
      exact SplitRestriction.keeps_positionEquiv_symm profile n σ c word

/-- The shuffling automorphism acts on every leg by the same permutation of word positions. -/
@[simp] theorem restrictedSplittingShuffle_partEquiv
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) (profile : SplitRestriction A)
    (σ : Equiv.Perm (Fin (n + 1))) (c : Leg) :
    (P.restrictedSplittingShuffle n profile σ).partEquiv c =
      positiveWordPositionEquiv (A c) n σ :=
  PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv P n σ c

/-- **Availability is permuted, not merely preserved.**  The shuffle sends supported block
addresses of `T^{⊗(n+1)}[α̃]` to supported block addresses. -/
theorem mem_restrictedSplittingPower_support_shuffle
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) (profile : SplitRestriction A)
    (σ : Equiv.Perm (Fin (n + 1)))
    {address : BlockAddress fun c ↦ PositiveWord (A c) n}
    (haddress : address ∈ (P.restrictedSplittingPower n profile).support) :
    (fun c ↦ positiveWordPositionEquiv (A c) n σ (address c)) ∈
      (P.restrictedSplittingPower n profile).support := by
  have h := PartitionedTensor.StructureRelabeling.mem_support_blockAddressCongr
    (P.restrictedSplittingShuffle n profile σ) haddress
  have heq : blockAddressCongr (P.restrictedSplittingShuffle n profile σ).partEquiv address =
      fun c ↦ positiveWordPositionEquiv (A c) n σ (address c) := by
    funext c
    rw [blockAddressCongr_apply, restrictedSplittingShuffle_partEquiv]
  rwa [heq] at h

end Tensor.PartitionedTensor

/-! ## Claim 3: the shuffling action on available blocks is uniform -/

/-- **The available small blocks on one leg.**  A block word of length `n + 1` is available for the
split distribution `α` exactly when its empirical type is `α`; these are `[DuanWuZhou2022]`'s
*available small Z-blocks* of a restricted-splitting power. -/
abbrev AvailableWord (I : Type w) [Fintype I] [DecidableEq I] (n : ℕ) (α : I → ℕ) :=
  {word : PositiveWord I n // WordType.multiplicity (positiveWordEquiv I n word) = α}

variable {I : Type w} [Fintype I] [DecidableEq I]

/-- **The shuffling action on available blocks.**  Position shuffling restricts to the available
blocks by Claim 1, so it is a permutation of them. -/
noncomputable def availableWordShuffle (n : ℕ) (α : I → ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (AvailableWord I n α) :=
  (positiveWordPositionEquiv I n σ).subtypePerm fun word ↦ by
    rw [multiplicity_positiveWordPositionEquiv]

@[simp] theorem availableWordShuffle_val (n : ℕ) (α : I → ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (word : AvailableWord I n α) :
    (availableWordShuffle n α σ word).1 = positiveWordPositionEquiv I n σ word.1 := rfl

/-- The number of shuffles carrying one available block to another does not depend on the target
block: the transporter is a translate of the stabilizer, and any two available blocks are related
by a position permutation because they have the same empirical type. -/
theorem card_availableWordShuffle_fiber (n : ℕ) (α : I → ℕ)
    (source target : AvailableWord I n α) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) ↦
        availableWordShuffle n α σ source = target).card =
      (WordShuffle.transporter (positiveWordEquiv I n source.1)
        (positiveWordEquiv I n source.1)).card := by
  classical
  have hset :
      (Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) ↦
          availableWordShuffle n α σ source = target) =
        WordShuffle.transporter (positiveWordEquiv I n source.1)
          (positiveWordEquiv I n target.1) := by
    ext σ
    rw [Finset.mem_filter, WordShuffle.mem_transporter]
    constructor
    · rintro ⟨-, hσ⟩
      have hval : positiveWordPositionEquiv I n σ source.1 = target.1 :=
        congrArg Subtype.val hσ
      rw [← hval, positiveWordEquiv_position_apply]
    · intro hσ
      refine ⟨Finset.mem_univ _, Subtype.ext ?_⟩
      apply (positiveWordEquiv I n).injective
      rw [availableWordShuffle_val, positiveWordEquiv_position_apply]
      exact hσ
  rw [hset]
  have htype : WordType.multiplicity (positiveWordEquiv I n target.1) =
      WordType.multiplicity (positiveWordEquiv I n source.1) := by
    rw [target.2, source.2]
  exact WordShuffle.card_transporter_eq_card_stabilizer _ _
    (WordType.positionPermOfSameMultiplicity (positiveWordEquiv I n target.1)
      (positiveWordEquiv I n source.1) htype)
    (WordType.positionPermOfSameMultiplicity_map _ _ htype)

/-- **`[DuanWuZhou2022]`, `hole_lemma.tex` Claim 3.**  A uniformly random position shuffle sends a
fixed available block to a uniformly distributed available block.

The paper proves this by exhibiting the orbit count `∏_t ∏_{k'} (α̃_t(k') · n_t)!`; the count is
not needed, only its independence of the two blocks, which is the transporter/stabilizer
translation in `card_availableWordShuffle_fiber`. -/
noncomputable def uniformOnAvailableWords (n : ℕ) (α : I → ℕ) :
    HoleRepair.UniformOnParts (Equiv.Perm (Fin (n + 1))) (AvailableWord I n α) :=
  HoleRepair.UniformOnParts.ofTargetIndependentFiber (availableWordShuffle n α) fun a b b' ↦ by
    rw [card_availableWordShuffle_fiber, card_availableWordShuffle_fiber]

@[simp] theorem uniformOnAvailableWords_relabel (n : ℕ) (α : I → ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (uniformOnAvailableWords n α).relabel σ = availableWordShuffle n α σ := rfl

/-! ## The Hole Lemma for restricted-splitting powers -/

/-- **`[DuanWuZhou2022]`'s Hole Lemma (Lemma 5.3) for a restricted-splitting power.**

`holes t` is the set of available Z-blocks destroyed in the `t`-th broken copy.  If

`|available| · ∏_t |holes t| < |available| ^ (number of copies)`

then the direct sum of the broken copies restricts onto the intact `T^{⊗(n+1)}[α̃]`.

Proof sketch, exactly the paper's: the shuffling group acts uniformly on the available blocks
(Claim 3), so the finite union bound `Combinatorics.exists_shuffles_avoiding` produces one shuffle
per copy after which every available block survives somewhere.  Each shuffle lifts to an
automorphism of the restricted power (Claim 2), so applying it to a broken copy yields the broken
copy with moved holes; the resulting covering is exactly the hypothesis of the layer-1 repair
`Restricts.indexedDirectSum_shuffledLegHoleRepair`, which zeroes out the duplicates and identifies
the copies.

Every step is a proved restriction or isomorphism; no relation between the assembled direct sum
and the target is assumed. -/
theorem Tensor.Restricts.indexedDirectSum_restrictedSplittingHoleRepair
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) (α : A Leg.Z → ℕ)
    (holes : ι → Finset (AvailableWord (A Leg.Z) n α))
    (hsmall : Fintype.card (AvailableWord (A Leg.Z) n α) * ∏ t, (holes t).card <
      Fintype.card (AvailableWord (A Leg.Z) n α) ^ Fintype.card ι) :
    Restricts
      (Tensor.indexedDirectSum
        (V := fun _ : ι ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
        fun t ↦ ((P.restrictedSplittingPower n (SplitRestriction.ofLeg Leg.Z α)).holeSelect
          Leg.Z fun word ↦ word ∈ (holes t).image Subtype.val).realize)
      (P.restrictedSplittingPower n (SplitRestriction.ofLeg Leg.Z α)).realize := by
  classical
  obtain ⟨shuffle, hshuffle⟩ :=
    exists_shuffles_avoiding (uniformOnAvailableWords (I := A Leg.Z) n α) holes hsmall
  set profile : SplitRestriction A := SplitRestriction.ofLeg Leg.Z α with hprofile
  set relabeling : ι → (P.restrictedSplittingPower n profile).StructureRelabeling :=
    fun t ↦ P.restrictedSplittingShuffle n profile (shuffle t).symm with hrelabeling
  -- The available type of the Z-word of any supported address.
  have havailable : ∀ address ∈ (P.restrictedSplittingPower n profile).support,
      WordType.multiplicity (positiveWordEquiv (A Leg.Z) n (address Leg.Z)) = α := by
    intro address haddress
    rw [PartitionedTensor.mem_restrictedSplittingPower_support] at haddress
    have hZ := haddress.2 Leg.Z
    rwa [SplitRestriction.keeps_some_iff
      (SplitRestriction.ofLeg_self (A := A) Leg.Z α)] at hZ
  -- Choose, for every available block, a copy in which it survives after shuffling.
  set pick : PositiveWord (A Leg.Z) n → ι := fun word ↦
    if h : WordType.multiplicity (positiveWordEquiv (A Leg.Z) n word) = α then
      (hshuffle ⟨word, h⟩).choose
    else Classical.arbitrary ι with hpick
  refine Restricts.indexedDirectSum_shuffledLegHoleRepair
    (P.restrictedSplittingPower n profile) Leg.Z relabeling
    (fun t word ↦ word ∈ (holes t).image Subtype.val) pick ?_
  intro address haddress
  have htype := havailable address haddress
  set available : AvailableWord (A Leg.Z) n α := ⟨address Leg.Z, htype⟩ with havailableDef
  have hpickValue : pick (address Leg.Z) = (hshuffle available).choose := by
    rw [hpick]
    simp only [dif_pos htype]
  have hnotMem :
      availableWordShuffle n α (shuffle (pick (address Leg.Z))) available ∉
        holes (pick (address Leg.Z)) := by
    rw [hpickValue]
    have h := (hshuffle available).choose_spec
    rwa [uniformOnAvailableWords_relabel] at h
  have hpartEquiv :
      ((relabeling (pick (address Leg.Z))).partEquiv Leg.Z).symm (address Leg.Z) =
        (availableWordShuffle n α (shuffle (pick (address Leg.Z))) available).1 := by
    rw [hrelabeling, PartitionedTensor.restrictedSplittingShuffle_partEquiv,
      positiveWordPositionEquiv_symm, Equiv.symm_symm, availableWordShuffle_val]
  rw [hpartEquiv]
  intro hmem
  obtain ⟨other, hother, hvalue⟩ := Finset.mem_image.mp hmem
  exact hnotMem (Subtype.ext hvalue ▸ hother)

/-! ## A tiny inhabited instance

The vacuity hazard flagged for this stage is that the *available* block set could be empty, which
would make every claim about the shuffling group true and useless.  `RestrictedSplittingPower.lean`
ships the corresponding tiny partition together with a surviving address and an excluded address;
this section shows that the shuffling automorphism is genuinely defined on that instance and that
it maps the surviving address to a surviving address.
-/

section TinyInstance

variable (K : Type u) [CommSemiring K]

/-- The shuffling automorphism of the tiny restricted-splitting power exists for every position
permutation. -/
noncomputable def tinyRestrictedSplittingShuffle (σ : Equiv.Perm (Fin 2)) :
    ((tinyPartition K).restrictedSplittingPower 1
      (SplitRestriction.ofLeg Leg.Z tinyMixedType)).StructureRelabeling :=
  (tinyPartition K).restrictedSplittingShuffle 1 (SplitRestriction.ofLeg Leg.Z tinyMixedType) σ

/-- **Availability really is permuted on a nonempty instance.**  The surviving mixed-type address
of the tiny restricted-splitting power is carried by every shuffle to a surviving address, so
Claim 1 is exercised on a support that is known to be inhabited. -/
theorem tiny_shuffle_mem_restrictedSplittingPower (σ : Equiv.Perm (Fin 2)) :
    (fun c ↦ positiveWordPositionEquiv (TinyLabel c) 1 σ (tinyMixedAddress c)) ∈
      ((tinyPartition K).restrictedSplittingPower 1
        (SplitRestriction.ofLeg Leg.Z tinyMixedType)).support :=
  PartitionedTensor.mem_restrictedSplittingPower_support_shuffle (tinyPartition K) 1 _ σ
    (tinyMixedAddress_mem_restrictedSplittingPower K)

end TinyInstance

end AlgebraicComplexity
