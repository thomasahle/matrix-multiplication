/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRegionalDivision
import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeAssembly

/-!
# Restricted-splitting tensor powers `T^{⊗n}[α̃]`

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module formalizes the
*restricted-splitting tensor power* introduced in

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§2.7, Definition 2.14 (`def:restricted_splitting`)**
> (`[DuanWuZhou2022]`),

together with the splitting degeneration that the paper calls `claim:degen`
(`component_value.tex`, Claim 7.1).

## The definition

`[DuanWuZhou2022]` §2.7 fixes a level-`ℓ` component `T_{i,j,k}`, views `T_{i,j,k}^{⊗n}` with its
induced level-`(ℓ−1)` partition, and *zeroes out every level-`(ℓ−1)` Z-variable block `Z_K̂` that is
not consistent with a prescribed Z-marginal split distribution `α̃`*.  The surviving subtensor is
written `T_{i,j,k}^{⊗n}[α̃]`.  The paper also uses the X- and Y-restricted variants
`T^{⊗n}[α̃^{(X)}]`, `T^{⊗n}[α̃^{(Y)}]` (§7 needs all three).

Formalized here at the level of an arbitrary partitioned tensor:

* the ambient object is `PartitionedTensor.positivePower P n`, whose block addresses are, on each
  leg independently, words of length `n+1` over that leg's block alphabet;
* "consistent with `α̃`" is "the word's empirical type is `α̃`", i.e.
  `WordType.multiplicity (positiveWordEquiv (A c) n word) = α̃`;
* `SplitRestriction A` records, **per leg**, either `none` (that leg is unrestricted) or
  `some α̃` (that leg's words must have empirical type `α̃`).  The paper's Z-only restriction is
  `SplitRestriction.ofLeg Leg.Z α̃`.

Zeroing out the remaining blocks is `PartitionedTensor.select` with a leg-local predicate, so the
ambient-to-restricted relation is the exact restriction `Tensor.Restricts.partitionedSelect`.

## The available block alphabet — and the vacuity hazard

The riskiest modelling decision here is *which* Z-blocks the restricted power is allowed to
contain.  If the alphabet is taken to be the whole fine alphabet rather than the `α̃`-consistent
part of it, every later count in `[DuanWuZhou2022]` (`|T_K|`, the bound `#available ≤ 2^{Nℓ}`, the
hole fraction) is silently wrong.  The formalization keeps the ambient alphabet — the address type
is unchanged, `fun c ↦ PositiveWord (A c) n` — and moves the restriction entirely into the
*support*, which is where `Tensor.Restricts.partitionedSelect` needs it.  `mem_… _support`
below is the exact membership criterion.

Because a support predicate that nothing satisfies would make every downstream statement vacuously
true, this module ships a tiny inhabited regression instance (`section TinyInstance`): a two-label
partition, its first positive power, an explicitly exhibited surviving mixed-type address, an
explicitly exhibited *excluded* constant-type address, and an instance of the splitting
degeneration.  This follows `DESIGN.md`'s tiny-client rule and the precedent of the `xIsolated`
vacuity trap found in the S6 campaign.

## Principal results

* `SplitRestriction`, `SplitRestriction.ofLeg`, `SplitRestriction.Keeps` — the restriction data
  and the leg-local keep predicate.
* `PartitionedTensor.restrictedSplittingPower` — the object `T^{⊗n}[α̃]`, with
  `mem_restrictedSplittingPower_support`.
* `Tensor.Restricts.power_restrictedSplittingPower` — `T^{⊗(n+1)} ⊵ T^{⊗(n+1)}[α̃]`: the
  restricted power is an exact restriction of the ambient tensor power, not merely of the
  partitioned power.
* `Tensor.Restricts.restrictedSplittingPower_binaryDivision` — **`[DuanWuZhou2022]`'s
  `claim:degen`**: if the parent type splits as a sum of the two segment types, the parent
  restricted power restricts onto the external product of the two segment restricted powers.  The
  paper states it for three segments with real weights `A₁ + A₂ + A₃ = 1`; the honest finite form
  is the binary one with *integral* types adding, which iterates
  (`Tensor.Restricts.restrictedSplittingPower_ternaryDivision`).
* `Tensor.Restricts.zRestrictedSplittingPower_binaryDivision` — the Z-only specialization the
  paper actually uses.

## Source-correction note

`claim:degen` is stated with real segment weights `A_r ∈ [0,1]`, `∑ A_r = 1`, and split
distributions satisfying `A₁ α̃^{[1]} + A₂ α̃^{[2]} + A₃ α̃^{[3]} = α̃`.  Read literally this is a
statement about *distributions*; the proof, however, zeroes out level-`ℓ` Z-blocks by the exact
type of each segment, which is a statement about *integral counts*.  The two agree only when
`A_r n` and `A_r n α̃^{[r]}` are integers.  The formalization therefore takes the integral form —
segment lengths `n`, `m` and types `β`, `γ` with `α̃ = β + γ` pointwise — from which the paper's
displayed real-weight statement follows whenever its own implicit integrality holds.  Nothing is
lost: `[DuanWuZhou2022]` only ever instantiates it at integral data.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w}

/-! ## Split restrictions -/

/-- **A split restriction**: for every tensor leg, either no constraint (`none`) or a prescribed
empirical type (`some α̃`) that the leg's block word must have.

`[DuanWuZhou2022]` restricts exactly one leg at a time (Z by default, X or Y in §7); that case is
`SplitRestriction.ofLeg`.  Allowing an independent option per leg costs nothing and makes the
splitting theorem below uniform in which legs are constrained. -/
abbrev SplitRestriction (A : Leg → Type w) := ∀ c, Option (A c → ℕ)

namespace SplitRestriction

/-- The split restriction constraining only the leg `c₀`, by the type `α`. -/
def ofLeg (c₀ : Leg) (α : A c₀ → ℕ) : SplitRestriction A :=
  fun c ↦ if h : c₀ = c then some (h ▸ α) else none

@[simp] theorem ofLeg_self (c₀ : Leg) (α : A c₀ → ℕ) : ofLeg c₀ α c₀ = some α := by
  simp [ofLeg]

theorem ofLeg_of_ne {c₀ c : Leg} (α : A c₀ → ℕ) (h : c₀ ≠ c) : ofLeg c₀ α c = none := by
  simp [ofLeg, h]

/-- **The leg-local keep predicate of a split restriction.**  A block word on leg `c` survives
when the leg is unrestricted, or when its empirical type is exactly the prescribed one. -/
def Keeps (profile : SplitRestriction A) (n : ℕ) :
    ∀ c, PositiveWord (A c) n → Prop :=
  fun c word ↦
    match profile c with
    | none => True
    | some α => WordType.multiplicity (positiveWordEquiv (A c) n word) = α

theorem keeps_of_none {profile : SplitRestriction A} {n : ℕ} {c : Leg}
    (h : profile c = none) (word : PositiveWord (A c) n) : profile.Keeps n c word := by
  simp [Keeps, h]

@[simp] theorem keeps_some_iff {profile : SplitRestriction A} {n : ℕ} {c : Leg}
    {α : A c → ℕ} (h : profile c = some α) (word : PositiveWord (A c) n) :
    profile.Keeps n c word ↔
      WordType.multiplicity (positiveWordEquiv (A c) n word) = α := by
  simp [Keeps, h]

/-- The keep predicate is decidable: block alphabets are finite with decidable equality, so
equality of empirical types is decidable.  The instance is noncomputable only because
`WordType.multiplicity` is. -/
noncomputable instance decidableKeeps (profile : SplitRestriction A) (n : ℕ) (c : Leg)
    (word : PositiveWord (A c) n) : Decidable (profile.Keeps n c word) := by
  classical
  exact Classical.dec _

end SplitRestriction

variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-! ## The restricted-splitting power -/

namespace Tensor.PartitionedTensor

/-- **The restricted-splitting tensor power `T^{⊗n}[α̃]`**
(`[DuanWuZhou2022]`, Definition 2.14).

The `(n+1)`-fold partitioned power of `P` with every block address whose word on a restricted leg
fails to have the prescribed empirical type zeroed out.  The block *alphabet* is unchanged; only
the support shrinks. -/
noncomputable def restrictedSplittingPower
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) (profile : SplitRestriction A) :
    PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n)
      (PositivePowerBlockSpace K V n) :=
  (P.positivePower n).select (profile.Keeps n)

/-- **The exact membership criterion for the restricted support.**  An address survives exactly
when it is an address of the ambient partitioned power and every restricted leg's word has the
prescribed empirical type. -/
@[simp] theorem mem_restrictedSplittingPower_support
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) (profile : SplitRestriction A)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n)) :
    address ∈ (P.restrictedSplittingPower n profile).support ↔
      address ∈ (P.positivePower n).support ∧ ∀ c, profile.Keeps n c (address c) :=
  PartitionedTensor.mem_select_support _ _ _

/-- The restricted power is a selection, hence its constituents are unchanged. -/
@[simp] theorem restrictedSplittingPower_constituent
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) (profile : SplitRestriction A) :
    (P.restrictedSplittingPower n profile).constituent =
      (P.positivePower n).constituent := rfl

end Tensor.PartitionedTensor

namespace Tensor.Restricts

/-- **The ambient partitioned power restricts onto the restricted-splitting power.**  This is the
zeroing-out of `[DuanWuZhou2022]`'s Definition 2.14, realized as an exact legwise restriction. -/
theorem partitionedPositivePower_restrictedSplittingPower
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) (profile : SplitRestriction A) :
    Restricts (P.positivePower n).realize
      (P.restrictedSplittingPower n profile).realize :=
  Tensor.Restricts.partitionedSelect (P.positivePower n) (profile.Keeps n)

/-- **`T^{⊗(n+1)} ⊵ T^{⊗(n+1)}[α̃]`.**  The restricted-splitting power is an exact restriction of
the ordinary tensor power of the realized partitioned tensor, not merely of its partitioned
repackaging. -/
theorem power_restrictedSplittingPower
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) (profile : SplitRestriction A) :
    Restricts (Tensor.power P.realize (n + 1))
      (P.restrictedSplittingPower n profile).realize :=
  (Tensor.Restricts.power_partitionedPositivePower P n).trans
    (partitionedPositivePower_restrictedSplittingPower P n profile)

end Tensor.Restricts

/-! ## `claim:degen`: splitting a restricted power into consecutive segments -/

section BinaryDivision

variable {n m : ℕ}

omit [∀ c, DecidableEq (A c)] in
/-- **A concatenated word has the prescribed parent type as soon as its two segments have the
prescribed segment types and the types add.**

Proof sketch: reconstruct the word as `positiveWordAppend` of its two pieces
(`Equiv.apply_symm_apply` for `positiveWordAppendEquiv`), then apply
`WordType.multiplicity_positiveWordAppend`. -/
theorem SplitRestriction.keeps_append
    {parent left right : SplitRestriction A}
    (hsum : ∀ c α, parent c = some α →
      ∃ β γ, left c = some β ∧ right c = some γ ∧ α = β + γ)
    (c : Leg) (word : PositiveWord (A c) (n + m + 1))
    (hleft : left.Keeps n c ((positiveWordAppendEquiv (A c) n m).symm word).1)
    (hright : right.Keeps m c ((positiveWordAppendEquiv (A c) n m).symm word).2) :
    parent.Keeps (n + m + 1) c word := by
  rcases hparent : parent c with _ | α
  · exact SplitRestriction.keeps_of_none hparent word
  obtain ⟨β, γ, hβ, hγ, hαβγ⟩ := hsum c α hparent
  rw [SplitRestriction.keeps_some_iff hparent]
  rw [SplitRestriction.keeps_some_iff hβ] at hleft
  rw [SplitRestriction.keeps_some_iff hγ] at hright
  set pieces := (positiveWordAppendEquiv (A c) n m).symm word with hpieces
  have happend : positiveWordAppend pieces.1 m pieces.2 = word := by
    rw [← positiveWordAppendEquiv_apply]
    exact (positiveWordAppendEquiv (A c) n m).apply_symm_apply word
  rw [← happend, WordType.multiplicity_positiveWordAppend, hleft, hright, hαβγ]

/-- **`[DuanWuZhou2022]`'s `claim:degen`, binary integral form.**

If the parent split type is, on every restricted leg, the pointwise sum of the two segment types,
then the parent restricted-splitting power restricts onto the external product of the two segment
restricted-splitting powers:

`T^{⊗(n+m+2)}[α̃] ⊵ T^{⊗(n+1)}[β] ⊗ T^{⊗(m+1)}[γ]` whenever `α̃ = β + γ`.

Proof sketch, following the paper: partition the `n+m+2` positions into a left segment of `n+1`
and a right segment of `m+1`, and zero out every surviving parent block whose left piece does not
have type `β` or whose right piece does not have type `γ`.  The resulting selection is legal —
that is, the extra zeroing is again a leg-local selection of the *parent* selection — precisely
because a block passing the segmentwise test already passes the parent test
(`SplitRestriction.keeps_append`).  What remains is the identification of the segmentwise
selection with the external product of the two segment powers, which is
`PartitionedTensor.appendPositiveWordPartitions_select` together with
`PartitionedTensor.appendPositiveWordPartitions_positivePowers`. -/
theorem Tensor.Restricts.restrictedSplittingPower_binaryDivision
    (P : PartitionedTensor (K := K) (A := A) V)
    (parent left right : SplitRestriction A)
    (hsum : ∀ c α, parent c = some α →
      ∃ β γ, left c = some β ∧ right c = some γ ∧ α = β + γ) :
    Restricts
      (P.restrictedSplittingPower (n + m + 1) parent).realize
      (Tensor.external
        (P.restrictedSplittingPower n left).realize
        (P.restrictedSplittingPower m right).realize) := by
  classical
  set parentKeep : ∀ c, PositiveWord (A c) (n + m + 1) → Prop := parent.Keeps (n + m + 1)
    with hparentKeep
  set leftKeep : ∀ c, PositiveWord (A c) n → Prop := left.Keeps n with hleftKeep
  set rightKeep : ∀ c, PositiveWord (A c) m → Prop := right.Keeps m with hrightKeep
  set segmentKeep : ∀ c, PositiveWord (A c) (n + m + 1) → Prop :=
    fun c word ↦
      leftKeep c ((positiveWordAppendEquiv (A c) n m).symm word).1 ∧
      rightKeep c ((positiveWordAppendEquiv (A c) n m).symm word).2 with hsegmentKeep
  set parentSelected := P.restrictedSplittingPower (n + m + 1) parent with hparentSelected
  set leftSelected := P.restrictedSplittingPower n left with hleftSelected
  set rightSelected := P.restrictedSplittingPower m right with hrightSelected
  set segmentSelected := (P.positivePower (n + m + 1)).select segmentKeep with hsegmentSelected
  have hsegment_parent : ∀ c word, segmentKeep c word → parentKeep c word := by
    intro c word hword
    exact SplitRestriction.keeps_append hsum c word hword.1 hword.2
  have hparent_select : parentSelected.select segmentKeep = segmentSelected := by
    apply PartitionedTensor.ext
    · apply Finset.ext
      intro address
      rw [PartitionedTensor.mem_select_support, hparentSelected,
        PartitionedTensor.restrictedSplittingPower, PartitionedTensor.mem_select_support,
        hsegmentSelected, PartitionedTensor.mem_select_support]
      constructor
      · rintro ⟨⟨hsupport, -⟩, hsegment⟩
        exact ⟨hsupport, hsegment⟩
      · rintro ⟨hsupport, hsegment⟩
        exact ⟨⟨hsupport, fun c ↦ hsegment_parent c (address c) (hsegment c)⟩, hsegment⟩
    · rfl
  have hparent_segment : Restricts parentSelected.realize segmentSelected.realize :=
    (Tensor.Restricts.partitionedSelect parentSelected segmentKeep).trans
      (Tensor.Restricts.of_eq (congrArg PartitionedTensor.realize hparent_select))
  have happend_selected :
      PartitionedTensor.appendPositiveWordPartitions leftSelected rightSelected =
        segmentSelected := by
    calc
      PartitionedTensor.appendPositiveWordPartitions leftSelected rightSelected =
          (PartitionedTensor.appendPositiveWordPartitions
            (P.positivePower n) (P.positivePower m)).select segmentKeep :=
        PartitionedTensor.appendPositiveWordPartitions_select
          (P.positivePower n) (P.positivePower m) leftKeep rightKeep
      _ = segmentSelected := by
        rw [P.appendPositiveWordPartitions_positivePowers n m]
  have hexternal_append :
      Isomorphic (Tensor.external leftSelected.realize rightSelected.realize)
        (PartitionedTensor.appendPositiveWordPartitions leftSelected rightSelected).realize :=
    (Tensor.Isomorphic.partitionedExternal leftSelected rightSelected).trans
      (Tensor.Isomorphic.partitionedReindex
        (leftSelected.external rightSelected)
        (fun c ↦ positiveWordAppendEquiv (A c) n m)
        (positivePowerBlockAppendEquivAt (K := K) (V := V) n m))
  refine hparent_segment.trans ?_
  have hsegment_append :
      Isomorphic segmentSelected.realize
        (PartitionedTensor.appendPositiveWordPartitions leftSelected rightSelected).realize := by
    rw [happend_selected]
    exact Tensor.Isomorphic.refl _
  exact (hsegment_append.trans hexternal_append.symm).restricts

/-- **`claim:degen` for three consecutive segments**, which is the arity `[DuanWuZhou2022]`
displays (`A₁ + A₂ + A₃ = 1`).  The intermediate split type of the last two segments is supplied
explicitly; iterating the binary form is exactly the paper's own argument, which zeroes out the
three segment types independently. -/
theorem Tensor.Restricts.restrictedSplittingPower_ternaryDivision
    (P : PartitionedTensor (K := K) (A := A) V) {p : ℕ}
    (parent first mid second third : SplitRestriction A)
    (hfirst : ∀ c α, parent c = some α →
      ∃ β γ, first c = some β ∧ mid c = some γ ∧ α = β + γ)
    (hmid : ∀ c α, mid c = some α →
      ∃ β γ, second c = some β ∧ third c = some γ ∧ α = β + γ) :
    Restricts
      (P.restrictedSplittingPower (n + (m + p + 1) + 1) parent).realize
      (Tensor.external
        (P.restrictedSplittingPower n first).realize
        (Tensor.external
          (P.restrictedSplittingPower m second).realize
          (P.restrictedSplittingPower p third).realize)) :=
  (Tensor.Restricts.restrictedSplittingPower_binaryDivision P parent first mid hfirst).trans
    (Tensor.Restricts.external (Tensor.Restricts.refl _)
      (Tensor.Restricts.restrictedSplittingPower_binaryDivision P mid second third hmid))

/-- **The Z-only specialization of `claim:degen`**, which is the form `[DuanWuZhou2022]` uses:
the Z-marginal split distribution of the parent is the sum of the two segments' Z-marginal split
distributions. -/
theorem Tensor.Restricts.zRestrictedSplittingPower_binaryDivision
    (P : PartitionedTensor (K := K) (A := A) V)
    (α β γ : A Leg.Z → ℕ) (hsum : α = β + γ) :
    Restricts
      (P.restrictedSplittingPower (n + m + 1) (SplitRestriction.ofLeg Leg.Z α)).realize
      (Tensor.external
        (P.restrictedSplittingPower n (SplitRestriction.ofLeg Leg.Z β)).realize
        (P.restrictedSplittingPower m (SplitRestriction.ofLeg Leg.Z γ)).realize) := by
  refine Tensor.Restricts.restrictedSplittingPower_binaryDivision P _ _ _ ?_
  intro c α' hα'
  rcases c with _ | _ | _
  · rw [SplitRestriction.ofLeg_of_ne α (by decide)] at hα'
    exact absurd hα' (by simp)
  · rw [SplitRestriction.ofLeg_of_ne α (by decide)] at hα'
    exact absurd hα' (by simp)
  · rw [SplitRestriction.ofLeg_self] at hα'
    refine ⟨β, γ, SplitRestriction.ofLeg_self _ _, SplitRestriction.ofLeg_self _ _, ?_⟩
    rw [← Option.some_inj.mp hα', hsum]

end BinaryDivision

/-! ## A tiny inhabited instance

`DESIGN.md` requires a deliberately tiny client for every major semantic operation.  For the
restricted-splitting power the specific failure mode to guard against is *vacuity*: a support
predicate that nothing satisfies makes every downstream statement about `T^{⊗n}[α̃]` true and
useless.  The instance below therefore exhibits, for the smallest interesting partition — two
block labels per leg, both supported on the diagonal — an address that **is** kept and an address
that **is not**, and then runs the splitting degeneration on them.
-/

section TinyInstance

variable (K : Type u) [CommSemiring K]

/-- Two block labels on every tensor leg. -/
abbrev TinyLabel : Leg → Type := fun _ ↦ Fin 2

/-- Every block of the tiny partition carries the ground ring on all three legs. -/
abbrev TinyBlockSpace : ∀ c, TinyLabel c → Type u := fun _ _ ↦ K

/-- The block address using the label `i` on every leg. -/
def tinyAddress (i : Fin 2) : BlockAddress TinyLabel := fun _ ↦ i

/-- A two-block partitioned tensor.  Its two supported addresses are the diagonal ones, and each
carries the rank-one tensor `1 ⊗ 1 ⊗ 1`. -/
noncomputable def tinyPartition :
    PartitionedTensor (K := K) (A := TinyLabel) (TinyBlockSpace K) where
  support := {tinyAddress 0, tinyAddress 1}
  constituent := fun _ ↦ Tensor.pure (K := K) (fun _ ↦ (1 : K))

@[simp] theorem tinyPartition_support :
    (tinyPartition K).support = {tinyAddress 0, tinyAddress 1} := rfl

/-- The one-letter positive word `i`. -/
def tinyLetter (i : Fin 2) : PositiveWord (Fin 2) 0 := i

/-- The empirical type of the one-letter word `i`: one occurrence of `i`, none of anything
else. -/
noncomputable def tinyLetterType (i : Fin 2) : Fin 2 → ℕ :=
  WordType.multiplicity (positiveWordEquiv (Fin 2) 0 (tinyLetter i))

theorem tinyLetterType_apply (i j : Fin 2) :
    tinyLetterType i j = if j = i then 1 else 0 := by
  have h := WordType.multiplicity_positiveWordConst (I := Fin 2) i 0
  exact congrFun h j

/-- The mixed length-two word `(0, 1)`, exhibited as the concatenation of the two one-letter
words. -/
def tinyMixedWord : PositiveWord (Fin 2) 1 :=
  positiveWordAppend (tinyLetter 0) 0 (tinyLetter 1)

/-- The constant length-two word `(0, 0)`. -/
def tinyConstantWord : PositiveWord (Fin 2) 1 :=
  positiveWordAppend (tinyLetter 0) 0 (tinyLetter 0)

/-- The split distribution "one `0` and one `1`", the empirical type of `tinyMixedWord`. -/
noncomputable def tinyMixedType : Fin 2 → ℕ := tinyLetterType 0 + tinyLetterType 1

theorem tinyMixedWord_type :
    WordType.multiplicity (positiveWordEquiv (Fin 2) 1 tinyMixedWord) = tinyMixedType :=
  WordType.multiplicity_positiveWordAppend (tinyLetter 0)
    (tinyLetter 1)

theorem tinyConstantWord_type :
    WordType.multiplicity (positiveWordEquiv (Fin 2) 1 tinyConstantWord) =
      tinyLetterType 0 + tinyLetterType 0 :=
  WordType.multiplicity_positiveWordAppend (tinyLetter 0)
    (tinyLetter 0)

/-- The two candidate types genuinely differ, so the restriction below is not the whole
support. -/
theorem tinyConstantType_ne_tinyMixedType :
    tinyLetterType 0 + tinyLetterType 0 ≠ tinyMixedType := by
  intro hcontra
  have h := congrFun hcontra 1
  simp [tinyMixedType, tinyLetterType_apply] at h

/-- The block address using `tinyMixedWord` on every leg. -/
def tinyMixedAddress : BlockAddress (fun c ↦ PositiveWord (TinyLabel c) 1) :=
  fun _ ↦ tinyMixedWord

/-- The block address using `tinyConstantWord` on every leg. -/
def tinyConstantAddress : BlockAddress (fun c ↦ PositiveWord (TinyLabel c) 1) :=
  fun _ ↦ tinyConstantWord

theorem tinyMixedAddress_mem_positivePower :
    tinyMixedAddress ∈ ((tinyPartition K).positivePower 1).support := by
  have h0 : tinyAddress 0 ∈ (tinyPartition K).support := by simp [tinyPartition]
  have h1 : tinyAddress 1 ∈ (tinyPartition K).support := by simp [tinyPartition]
  exact (PartitionedTensor.mem_external_support ((tinyPartition K).positivePower 0)
    (tinyPartition K) tinyMixedAddress).mpr ⟨h0, h1⟩

theorem tinyConstantAddress_mem_positivePower :
    tinyConstantAddress ∈ ((tinyPartition K).positivePower 1).support := by
  have h0 : tinyAddress 0 ∈ (tinyPartition K).support := by simp [tinyPartition]
  exact (PartitionedTensor.mem_external_support ((tinyPartition K).positivePower 0)
    (tinyPartition K) tinyConstantAddress).mpr ⟨h0, h0⟩

/-- **The tiny restricted-splitting power is inhabited.**  The mixed-type address survives the
Z-restriction to the split distribution `tinyMixedType`. -/
theorem tinyMixedAddress_mem_restrictedSplittingPower :
    tinyMixedAddress ∈
      ((tinyPartition K).restrictedSplittingPower 1
        (SplitRestriction.ofLeg Leg.Z tinyMixedType)).support := by
  rw [PartitionedTensor.mem_restrictedSplittingPower_support]
  refine ⟨tinyMixedAddress_mem_positivePower K, ?_⟩
  intro c
  rcases c with _ | _ | _
  · exact SplitRestriction.keeps_of_none
      (SplitRestriction.ofLeg_of_ne (A := TinyLabel) tinyMixedType (by decide)) _
  · exact SplitRestriction.keeps_of_none
      (SplitRestriction.ofLeg_of_ne (A := TinyLabel) tinyMixedType (by decide)) _
  · rw [SplitRestriction.keeps_some_iff (SplitRestriction.ofLeg_self (A := TinyLabel) Leg.Z tinyMixedType)]
    exact tinyMixedWord_type

/-- **The tiny restricted-splitting power is a proper restriction.**  The constant-type address
is an address of the ambient power but does not survive the Z-restriction, so the restriction is
neither vacuous nor trivial. -/
theorem tinyConstantAddress_not_mem_restrictedSplittingPower :
    tinyConstantAddress ∉
      ((tinyPartition K).restrictedSplittingPower 1
        (SplitRestriction.ofLeg Leg.Z tinyMixedType)).support := by
  rw [PartitionedTensor.mem_restrictedSplittingPower_support]
  rintro ⟨-, hkeep⟩
  have hZ := hkeep Leg.Z
  rw [SplitRestriction.keeps_some_iff
    (SplitRestriction.ofLeg_self (A := TinyLabel) Leg.Z tinyMixedType)] at hZ
  have hZ' : WordType.multiplicity (positiveWordEquiv (Fin 2) 1 tinyConstantWord) =
      tinyMixedType := hZ
  rw [tinyConstantWord_type] at hZ'
  exact tinyConstantType_ne_tinyMixedType hZ' 

/-- **The splitting degeneration, exercised on the tiny instance.**  The two one-letter split
distributions add to `tinyMixedType`, so the mixed restricted power restricts onto the external
product of the two single-letter restricted powers. -/
theorem tiny_restrictedSplittingPower_binaryDivision :
    Restricts
      ((tinyPartition K).restrictedSplittingPower 1
        (SplitRestriction.ofLeg Leg.Z tinyMixedType)).realize
      (Tensor.external
        ((tinyPartition K).restrictedSplittingPower 0
          (SplitRestriction.ofLeg Leg.Z (tinyLetterType 0))).realize
        ((tinyPartition K).restrictedSplittingPower 0
          (SplitRestriction.ofLeg Leg.Z (tinyLetterType 1))).realize) :=
  Tensor.Restricts.zRestrictedSplittingPower_binaryDivision (n := 0) (m := 0)
    (tinyPartition K) tinyMixedType (tinyLetterType 0) (tinyLetterType 1) rfl

end TinyInstance

end AlgebraicComplexity
