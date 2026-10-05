/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoJointHashing

/-!
# The plain fifteen-letter hashing encoding of the coarse square

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]` hashes a plain power
(`global_value.tex:12`; `sym₆` lives only in the value functional, `prelim.tex:142-146`), so the
encoding the hash needs is the one for the *fifteen* coarse Coppersmith--Winograd square
addresses, not the `15 ^ 6` six-tuples.

`dwz63SquareHashEncoding` is that encoding.  It is the base `cwSquareNatEncoding` --- radix `5`,
constant target `4`, the degree-four antidiagonal --- read at the square partition's own support
by `dwz63SquareNatEncoding` and cast once into the field.

## What the plain alphabet buys

The six-orientation encoding composed six base-five digits, so its radix was `5 ^ 6 = 15625` and
every client carried the characteristic floor `15625 ≤ p`.  Here the radix is `5`, so the floor is

`5 ≤ p`,

and the modulus requirement in `exists_seed_…_of_modulus` is `8 * d ≤ Fintype.card R` at the
*plain* leg-fiber degree.  The `15625` quoted in the six-orientation modules is not a feature of
the construction; it was the price of hashing the `15 ^ 6`-block object.

## The alphabet bridge

The typical-count lane states its counts over the bare `↥cwSquareSupport` rather than
`(cwSquarePartitionedTensor K dwz63Q).support`, deliberately, to keep the `whnf` wall out of its
modules.  The two are **definitionally equal** --- `cwSquarePartitionedTensor_support` is `rfl`
(`Examples/CoppersmithWinogradSquare.lean:307-309`) --- so the bridge costs nothing, and
`dwz63SquareHashEncodingBare` records it in one place: it is the same term at the other ascription.

## This module is an adapter, not a second encoding

**`cwSquarePartitionHashEncoding` (`Examples/CoppersmithWinogradSquareCounting.lean:73`) is the
canonical hashing encoding of the coarse square.**  `dwz63SquareHashEncoding` below is retained
*only* as the thin `5 ≤ p` adapter that feeds it: it exposes the side condition as the
characteristic floor the level-two clients quote instead of as an injectivity hypothesis.  The two
are interconvertible --- `cwSquareFieldValue_zmod_injective`
(`Examples/CoppersmithWinogradSquareOuterCounting.lean:221`) discharges the canonical encoding's
`Function.Injective (cwSquareFieldValue (R := R))` from exactly the `5 ≤ M` floor --- and there is
deliberately no second definition of this object anywhere in the tree.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-! ## The plain natural-number encoding, at radix five -/

/-- **The plain alphabet is `5`**, against `5 ^ 6 = 15625` for the six-orientation encoding. -/
@[simp] theorem dwz63SquareNatEncoding_alphabet (K : Type u) [CommRing K] :
    (dwz63SquareNatEncoding K).alphabet = 5 := rfl

/-- **The plain constant target is `4`**, the degree-four antidiagonal. -/
@[simp] theorem dwz63SquareNatEncoding_natTarget (K : Type u) [CommRing K] :
    (dwz63SquareNatEncoding K).natTarget = 4 := rfl

/-! ## The field-valued encoding -/

/-- **The plain fifteen-letter hashing encoding.**  Any field of characteristic at least `5`
carries it. -/
noncomputable def dwz63SquareHashEncoding (K : Type u) [CommRing K]
    (R : Type v) [Field R] {p : ℕ} [CharP R p] (hp : 5 ≤ p) :
    PartitionHashEncoding (R := R) ((cwSquarePartitionedTensor K dwz63Q).support) :=
  (dwz63SquareNatEncoding K).toPartitionHashEncoding (R := R) (p := p)
    (by rw [dwz63SquareNatEncoding_alphabet]; exact hp)

/-- The hashing target is the constant `4`. -/
@[simp] theorem dwz63SquareHashEncoding_target (K : Type u) [CommRing K]
    (R : Type v) [Field R] {p : ℕ} [CharP R p] (hp : 5 ≤ p) :
    (dwz63SquareHashEncoding K R hp).target = ((4 : ℕ) : R) := by
  unfold dwz63SquareHashEncoding
  rw [NatBlockEncoding.toPartitionHashEncoding_target, dwz63SquareNatEncoding_natTarget]

/-! ## The alphabet bridge, in one place -/

/-- **The two alphabet ascriptions are definitionally equal.**  The typical-count lane may state
its counts over the bare `cwSquareSupport`; nothing has to be transported. -/
theorem cwSquarePartitionedTensor_support_dwz63Q (K : Type u) [CommRing K] :
    (cwSquarePartitionedTensor K dwz63Q).support = cwSquareSupport := rfl

/-- **The same encoding, read at the bare fifteen-address alphabet.**  This is the form the
typical-count lane consumes; it is the identical term, re-ascribed. -/
noncomputable def dwz63SquareHashEncodingBare (K : Type u) [CommRing K]
    (R : Type v) [Field R] {p : ℕ} [CharP R p] (hp : 5 ≤ p) :
    PartitionHashEncoding (R := R) cwSquareSupport :=
  dwz63SquareHashEncoding K R hp

theorem dwz63SquareHashEncodingBare_eq (K : Type u) [CommRing K]
    (R : Type v) [Field R] {p : ℕ} [CharP R p] (hp : 5 ≤ p) :
    dwz63SquareHashEncodingBare K R hp = dwz63SquareHashEncoding K R hp := rfl

end AlgebraicComplexity.Examples
