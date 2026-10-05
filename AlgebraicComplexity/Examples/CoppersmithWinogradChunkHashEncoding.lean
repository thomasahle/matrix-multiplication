/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibility
import AlgebraicComplexity.Examples.CoppersmithWinogradHashEncoding

/-!
# Hash encoding for Coppersmith--Winograd chunks

The ordinary CW block alphabet is encoded by the ternary digits `0,1,2`.  A depth-`d` native CW
chunk is a word of `2 ^ d` such blocks, and reading that word as a `2 ^ d`-digit base-three
numeral gives an injective label in `{0,\ldots,3 ^ 2 ^ d - 1}`.  Supported triples have digit sum
two *at every split position*, so their three codes sum to the constant
`cwChunkNatTarget d = \sum_i 2 \cdot 3 ^ i`.

Consequently every field whose characteristic is at least `cwChunkAlphabetSize d = 3 ^ 2 ^ d`
supplies the tight injective partition encoding required by the generic marked hashing theorem.
The characteristic bound is a constant in `d`; it has no asymptotic cost in the later prime-field
construction, where `PrimeFieldSizing.loss` absorbs it.

## Layout

* the positional base-`b` code `natBaseCode` and its four arithmetic lemmas, in the root
  `AlgebraicComplexity` namespace because nothing about them is CW-specific;
* the depth-generic chunk encoding, culminating in `cwChunkPartitionHashEncoding`;
* the paper-level-two specialization at `depth = 1`, whose `cwLevelTwo…` names are the ones the
  committed level-two inner hashing construction consumes.  Their *definitions* are written out
  independently — the level-two code is the two-digit expression `d₀ + 3 · d₁`, which is only
  propositionally (not definitionally) the generic sum, and the level-two consumer relies on the
  short form.  Their *proofs* are one-line corollaries of the generic ones, with
  `cwChunkNatCode_one` and `cwChunkNatTarget_one` as the two regression pins that make the
  specialization safe.
-/

namespace AlgebraicComplexity

open scoped BigOperators

/-! ## Positional base-`b` codes on a finite digit string -/

/-- Positional base-`b` value of a finite digit string, least significant digit first. -/
def natBaseCode (b : ℕ) {N : ℕ} (d : Fin N → ℕ) : ℕ :=
  ∑ i, d i * b ^ (i : ℕ)

@[simp] theorem natBaseCode_empty (b : ℕ) (d : Fin 0 → ℕ) : natBaseCode b d = 0 := by
  simp [natBaseCode]

/-- Peel off the least significant digit of a positional base-`b` code. -/
theorem natBaseCode_succ (b : ℕ) {N : ℕ} (d : Fin (N + 1) → ℕ) :
    natBaseCode b d = d 0 + b * natBaseCode b (fun i : Fin N ↦ d i.succ) := by
  unfold natBaseCode
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · simp
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [Fin.val_succ, pow_succ]
    ring

/-- A base-`b` numeral with `N` digits is below `b ^ N`.

Proof sketch: induction on `N`.  The tail is below `b ^ N`, hence at most `b ^ N - 1`; multiplying
by `b` and adding a leading digit below `b` stays below `b ^ (N + 1)`. -/
theorem natBaseCode_lt (b : ℕ) :
    ∀ (N : ℕ) (d : Fin N → ℕ), (∀ i, d i < b) → natBaseCode b d < b ^ N := by
  intro N
  induction N with
  | zero => intro d _; simp [natBaseCode]
  | succ N ih =>
      intro d hd
      have hsub : natBaseCode b (fun i : Fin N ↦ d i.succ) < b ^ N :=
        ih _ (fun i ↦ hd i.succ)
      have h0 := hd 0
      rw [natBaseCode_succ]
      calc d 0 + b * natBaseCode b (fun i : Fin N ↦ d i.succ)
          < b + b * natBaseCode b (fun i : Fin N ↦ d i.succ) := by omega
        _ = b * (natBaseCode b (fun i : Fin N ↦ d i.succ) + 1) := by ring
        _ ≤ b * b ^ N := Nat.mul_le_mul le_rfl hsub
        _ = b ^ (N + 1) := by ring

/-- Base-`b` numerals of a fixed length determine their digits.

Proof sketch: induction on `N`.  Reducing the code modulo `b` isolates the least significant
digit; cancelling `b` from the remainder leaves the tail codes equal. -/
theorem natBaseCode_inj (b : ℕ) :
    ∀ (N : ℕ) (d e : Fin N → ℕ), (∀ i, d i < b) → (∀ i, e i < b) →
      natBaseCode b d = natBaseCode b e → d = e := by
  intro N
  induction N with
  | zero => intro d e _ _ _; funext i; exact i.elim0
  | succ N ih =>
      intro d e hd he h
      have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) (hd 0)
      rw [natBaseCode_succ, natBaseCode_succ] at h
      have h0 : d 0 = e 0 := by
        have hmod := congrArg (fun value : ℕ ↦ value % b) h
        simp only [Nat.add_mul_mod_self_left] at hmod
        rwa [Nat.mod_eq_of_lt (hd 0), Nat.mod_eq_of_lt (he 0)] at hmod
      have hmul : b * natBaseCode b (fun i : Fin N ↦ d i.succ) =
          b * natBaseCode b (fun i : Fin N ↦ e i.succ) := by omega
      have htail := Nat.eq_of_mul_eq_mul_left hb hmul
      have hrec := ih _ _ (fun i ↦ hd i.succ) (fun i ↦ he i.succ) htail
      funext i
      refine Fin.cases ?_ ?_ i
      · exact h0
      · intro j
        exact congrFun hrec j

/-- Positional codes add coordinatewise. -/
theorem natBaseCode_add_three (b : ℕ) {N : ℕ} (x y z : Fin N → ℕ) :
    natBaseCode b x + natBaseCode b y + natBaseCode b z =
      natBaseCode b (fun i ↦ x i + y i + z i) := by
  unfold natBaseCode
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring
end AlgebraicComplexity

namespace AlgebraicComplexity.Examples

open scoped BigOperators
open AlgebraicComplexity Tensor

universe u v

/-! ## Depth-generic base-three chunk hash encoding -/

/-- Number of distinct depth-`depth` native CW chunk labels, `3 ^ 2 ^ depth`.

At depth one this is `9`, the constant appearing in `cwLevelTwoChunkPartitionHashEncoding`. -/
def cwChunkAlphabetSize (depth : ℕ) : ℕ := 3 ^ 2 ^ depth

theorem two_le_cwChunkAlphabetSize (depth : ℕ) : 2 ≤ cwChunkAlphabetSize depth := by
  have h : (3 : ℕ) ^ 1 ≤ 3 ^ 2 ^ depth :=
    Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  rw [pow_one] at h
  exact le_trans (by norm_num) h

@[simp] theorem cwChunkAlphabetSize_one : cwChunkAlphabetSize 1 = 9 := by
  norm_num [cwChunkAlphabetSize]

/-- Positional base-three value of a complete-split chunk word. -/
def splitWordCode {depth : ℕ} (word : SplitWord depth) : ℕ :=
  natBaseCode 3 (fun i ↦ (word i : ℕ))

theorem splitWordCode_lt {depth : ℕ} (word : SplitWord depth) :
    splitWordCode word < cwChunkAlphabetSize depth :=
  natBaseCode_lt 3 (2 ^ depth) _ (fun i ↦ (word i).isLt)

theorem splitWordCode_injective (depth : ℕ) :
    Function.Injective (splitWordCode (depth := depth)) := by
  intro x y h
  have hdigits := natBaseCode_inj 3 (2 ^ depth)
    (fun i ↦ ((x i : ℕ))) (fun i ↦ ((y i : ℕ)))
    (fun i ↦ (x i).isLt) (fun i ↦ (y i).isLt) h
  funext i
  exact Fin.ext (congrFun hdigits i)

/-- Natural base-three code of a native depth-`depth` CW chunk. -/
def cwChunkNatCode (depth : ℕ) (word : PositiveWord CWBlock (2 ^ depth - 1)) : ℕ :=
  splitWordCode (cwChunkSplitWord depth word)

theorem cwChunkNatCode_lt (depth : ℕ) (word : PositiveWord CWBlock (2 ^ depth - 1)) :
    cwChunkNatCode depth word < cwChunkAlphabetSize depth :=
  splitWordCode_lt _

theorem cwChunkNatCode_injective (depth : ℕ) :
    Function.Injective (cwChunkNatCode depth) := fun _x _y h ↦
  cwChunkSplitWord_injective depth (splitWordCode_injective depth h)

/-- Constant coordinate sum of the three base-three chunk codes on a supported address.

At depth one this is `2 + 3 * 2 = 8`. -/
def cwChunkNatTarget (depth : ℕ) : ℕ :=
  natBaseCode 3 (fun _ : Fin (2 ^ depth) ↦ 2)

/-- Regression: at depth one the generic target is the level-two constant `8`. -/
@[simp] theorem cwChunkNatTarget_one : cwChunkNatTarget 1 = 8 := by decide

/-- On every supported depth-`depth` chunk address, the three natural codes sum to
`cwChunkNatTarget depth`.

Proof sketch: the CW support condition holds *at every split position*, so the three digit strings
add to the constant string `2`; positional codes add coordinatewise. -/
theorem cwChunkNatCode_sum
    (K : Type u) [CommRing K] (q depth : ℕ)
    (address : BlockAddress (fun _c ↦ PositiveWord CWBlock (2 ^ depth - 1)))
    (haddress : address ∈ (cwChunkPartitionedTensor K q depth).support) :
    cwChunkNatCode depth (address .X) +
        cwChunkNatCode depth (address .Y) +
        cwChunkNatCode depth (address .Z) = cwChunkNatTarget depth := by
  have hlegal := cwChunkPartitionedTensor_isEncodedFineLegalOnSupport K q depth
    address haddress
  unfold cwChunkNatCode splitWordCode cwChunkNatTarget
  rw [natBaseCode_add_three]
  refine congrArg (natBaseCode 3) ?_
  funext i
  exact hlegal i

/-- Field-valued base-three chunk code. -/
def cwChunkFieldValue {R : Type v} [Field R] (depth : ℕ)
    (word : PositiveWord CWBlock (2 ^ depth - 1)) : R :=
  (cwChunkNatCode depth word : ℕ)

/-- A characteristic bound of `cwChunkAlphabetSize depth` makes the field-valued chunk code
injective. -/
theorem cwChunkFieldValue_injective
    {R : Type v} [Field R] {p : ℕ} [CharP R p] {depth : ℕ}
    (hp : cwChunkAlphabetSize depth ≤ p) :
    Function.Injective (cwChunkFieldValue (R := R) depth) := by
  intro left right h
  apply cwChunkNatCode_injective depth
  apply CharP.natCast_injOn_Iio R p
  · exact (cwChunkNatCode_lt depth left).trans_le hp
  · exact (cwChunkNatCode_lt depth right).trans_le hp
  · exact h

/-- The support of the depth-`depth` CW chunk partition is nonempty.

Proof sketch: the constant word `cw200 ⋯ cw200` of length `2 ^ depth - 1` is supported, because
`cw200` is a supported CW block and the positive power's support is the image of the supported
words.  (Downstream, `cwChunkSupportWitness` packages the same witness as a term; that module is a
sibling of this one, so the witness is rebuilt here rather than imported.) -/
theorem cwChunkSupport_nonempty (K : Type u) [CommRing K] (q depth : ℕ) :
    (cwChunkPartitionedTensor K q depth).support.Nonempty := by
  classical
  let base : (cwPartitionedTensor K q).support := ⟨cw200, by
    change cw200 ∈ cwBlockSupport
    decide⟩
  let word : PositiveWord (cwPartitionedTensor K q).support (2 ^ depth - 1) :=
    positiveWordConst base (2 ^ depth - 1)
  refine ⟨positiveSupportWordBlockAddress
    (cwPartitionedTensor K q).support (2 ^ depth - 1) word, ?_⟩
  change _ ∈ ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).support
  rw [(cwPartitionedTensor K q
    ).positivePower_support_eq_image_positiveSupportWordBlockAddress]
  exact Finset.mem_image.mpr ⟨word, Finset.mem_univ _, rfl⟩

/-- Tight injective hashing encoding for the depth-`depth` CW chunk partition.

This is the depth-generic replacement for `cwLevelTwoChunkPartitionHashEncoding`; the only change
is that the characteristic floor grows from `9` to the constant `cwChunkAlphabetSize depth`. -/
def cwChunkPartitionHashEncoding
    (K : Type u) [CommRing K] (q depth : ℕ)
    {R : Type v} [Field R] {p : ℕ} [CharP R p]
    (hp : cwChunkAlphabetSize depth ≤ p) :
    PartitionHashEncoding (R := R) (cwChunkPartitionedTensor K q depth).support where
  encode _c := cwChunkFieldValue depth
  target := (cwChunkNatTarget depth : ℕ)
  support_nonempty := cwChunkSupport_nonempty K q depth
  encode_injective _c := cwChunkFieldValue_injective hp
  legal address haddress := by
    have hsum := cwChunkNatCode_sum K q depth address haddress
    have hcast := congrArg (fun value : ℕ ↦ (value : R)) hsum
    simpa [cwChunkFieldValue, Nat.cast_add] using hcast

/-! ## The paper-level-two specialization -/

/-- Natural base-three code of an ordered pair of CW block labels. -/
def cwLevelTwoChunkNatCode (word : PositiveWord CWBlock 1) : ℕ :=
  (cwBlockDigit word.1 : ℕ) + 3 * (cwBlockDigit word.2 : ℕ)

/-- Regression: at depth one the generic code is literally `cwLevelTwoChunkNatCode`.  This pins
down the position convention of `cwChunkSplitWord` against the existing level-two encoding. -/
theorem cwChunkNatCode_one (word : PositiveWord CWBlock 1) :
    cwChunkNatCode 1 word = cwLevelTwoChunkNatCode word := by
  obtain ⟨a, b⟩ := word
  cases a <;> cases b <;> decide

/-- The chunk code lies in the nine-letter alphabet. -/
def cwLevelTwoChunkCode (word : PositiveWord CWBlock 1) : Fin 9 :=
  ⟨cwLevelTwoChunkNatCode word, by
    rcases word with ⟨left, right⟩
    cases left <;> cases right <;> decide⟩

/-- Base-three coding is injective on ordered pairs of CW blocks.

Deliberately *not* a corollary of `cwChunkNatCode_injective` at `depth = 1`.  The generic route runs
through `natBaseCode_inj`, whose `Finset.sum` reasoning pulls in `Classical.choice`; the finite
case split below needs no choice, and this is the only declaration in the level-two family whose
`#print axioms` output would grow.  Keeping it leaves that output exactly as audited. -/
theorem cwLevelTwoChunkCode_injective : Function.Injective cwLevelTwoChunkCode := by
  rintro ⟨left₁, right₁⟩ ⟨left₂, right₂⟩ h
  cases left₁ <;> cases right₁ <;> cases left₂ <;> cases right₂ <;>
    simp_all [cwLevelTwoChunkCode, cwLevelTwoChunkNatCode, cwBlockDigit] <;> rfl

/-- Field-valued two-letter chunk code. -/
def cwLevelTwoChunkFieldValue
    {R : Type v} [Field R] (word : PositiveWord CWBlock 1) : R :=
  (cwLevelTwoChunkCode word : ℕ)

/-- At depth one the generic field-valued code is the level-two one. -/
theorem cwChunkFieldValue_one {R : Type v} [Field R] :
    cwChunkFieldValue (R := R) 1 = cwLevelTwoChunkFieldValue (R := R) := by
  funext word
  unfold cwChunkFieldValue cwLevelTwoChunkFieldValue
  rw [cwChunkNatCode_one]
  rfl

/-- A characteristic bound of nine makes the field-valued chunk code injective. -/
theorem cwLevelTwoChunkFieldValue_injective
    {R : Type v} [Field R] {p : ℕ} [CharP R p] (hp : 9 ≤ p) :
    Function.Injective (cwLevelTwoChunkFieldValue (R := R)) := by
  rw [← cwChunkFieldValue_one (R := R)]
  exact cwChunkFieldValue_injective (by simpa using hp)

/-- On every supported two-letter chunk address, the three natural codes sum to eight. -/
theorem cwLevelTwoChunkNatCode_sum
    (K : Type u) [CommRing K] (q : ℕ)
    (address : BlockAddress (fun _c ↦ PositiveWord CWBlock 1))
    (haddress : address ∈ (cwChunkPartitionedTensor K q 1).support) :
    cwLevelTwoChunkNatCode (address .X) +
        cwLevelTwoChunkNatCode (address .Y) +
        cwLevelTwoChunkNatCode (address .Z) = 8 := by
  have hsum := cwChunkNatCode_sum K q 1 address haddress
  rwa [cwChunkNatCode_one, cwChunkNatCode_one, cwChunkNatCode_one,
    cwChunkNatTarget_one] at hsum

/-- The support of the two-letter CW chunk partition is nonempty. -/
theorem cwLevelTwoChunkSupport_nonempty
    (K : Type u) [CommRing K] (q : ℕ) :
    (cwChunkPartitionedTensor K q 1).support.Nonempty :=
  cwChunkSupport_nonempty K q 1

/-- Tight injective hashing encoding for the paper-level-two CW chunk partition. -/
def cwLevelTwoChunkPartitionHashEncoding
    (K : Type u) [CommRing K] (q : ℕ)
    {R : Type v} [Field R] {p : ℕ} [CharP R p] (hp : 9 ≤ p) :
    PartitionHashEncoding (R := R) (cwChunkPartitionedTensor K q 1).support where
  encode _c := cwLevelTwoChunkFieldValue
  target := 8
  support_nonempty := cwLevelTwoChunkSupport_nonempty K q
  encode_injective _c := cwLevelTwoChunkFieldValue_injective hp
  legal address haddress := by
    have hsum := cwLevelTwoChunkNatCode_sum K q address haddress
    have hcast := congrArg (fun value : ℕ ↦ (value : R)) hsum
    simpa [cwLevelTwoChunkFieldValue, cwLevelTwoChunkCode,
      Nat.cast_add] using hcast

end AlgebraicComplexity.Examples
