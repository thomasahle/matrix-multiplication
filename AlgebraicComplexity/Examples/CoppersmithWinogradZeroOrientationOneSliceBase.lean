/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquareSymmetryDefs
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOneSliceBase
import AlgebraicComplexity.Examples.CoppersmithWinogradChunkDimension
import AlgebraicComplexity.MatrixMultiplication.OneSliceRestrictionTransport
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientation

/-!
# One-slice bases for the zero-`X` and zero-`Y` Coppersmith--Winograd constituents

`CoppersmithWinogradZeroOneSliceBase` certifies the three base CW constituents whose **`Z`** block
is `zero` — `cw200`, `cw020` and `cw110` — as one-slice tensors `⟨1, d, 1⟩`, by explicit finite
coordinate proofs.  A laser certificate meets zero blocks in all three orientations, so the same
certificates are needed for the zero-`X` family `{cw020, cw002, cw011}` and the zero-`Y` family
`{cw200, cw002, cw101}`.

**No new finite coordinate proof occurs here.**  The committed cyclic symmetry
`cwConstituentOfBlocks_cycle` already carries every *supported* base constituent onto the
constituent with rotated block labels, and that rotation sends each zero-`X` and each zero-`Y`
address to a zero-`Z` one:

| zero leg | orientation | `cw002` | `cw011` / `cw101` | third address |
|---|---|---|---|---|
| `X` | `zeroOrientation .X = cycle.symm` | `↦ cw020` | `cw011 ↦ cw110` | `cw020 ↦ cw200` |
| `Y` | `zeroOrientation .Y = cycle` | `↦ cw200` | `cw101 ↦ cw110` | `cw200 ↦ cw020` |
| `Z` | `zeroOrientation .Z = 1` | — | — | the committed certificates |

So the `X`- and `Y`-side bases are **transports** of the committed `Z`-side ones along
`OneSliceRestriction.precompose`, not re-proofs.

## The conclusion stays in the permuted frame

A one-slice target `⟨1, d, 1⟩` is not preserved by a leg rotation, so the certificates below are
certificates of the **rotated source** `Tensor.permute (zeroOrientation zero) …` against the
*unrotated* `⟨1, d, 1⟩`.  This is the ratified items-1--2 design decision applied at the leaf: every
statement names its rotation, so a client cannot pair a rotated constituent with an unrotated leaf
dimension by accident.  The surviving matrix dimension is read at `secondLiveLeg zero`, which is
`.Y` exactly when `zero = .Z` — recovering the committed convention as the identity instance.

## What is new, and what it costs

Only `cwConstituentOfBlocks_cycleSymm`: the committed file states the rotation for `cycle` and for
the `Y`/`Z` transposition `xzy`, and the zero-`X` orientation needs the third one, `cycle.symm`.
It is the same forty-line pattern as `cwConstituentOfBlocks_cycle`, on the same six supported
addresses.  Deriving it from the committed theorem instead is *not* possible without a dependent
rewrite: `permute cycle (permute cycle T)` has leg-space family
`fun c ↦ V (cycle.symm (cycle.symm c))`, which is only propositionally — never definitionally —
the family `fun c ↦ V (cycle c)` of `permute cycle.symm T`.

`cwBaseConstituentCycleEquiv`, `cwConstituentOfBlocks_cycle` and their pure-tensor lemma are the
only things this module needs from `CoppersmithWinogradSquareSymmetryDefs`; the remaining fourteen
hundred lines of that file are about the CW *square*.  Splitting those seventy-five lines into a
lightweight base-symmetry core is the one consolidation this module suggests, and it is left to a
later pass rather than taken here, because editing the committed file is out of scope.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-! ## The third rotation of the base constituents -/

/-- Retype a base CW constituent permuted by `cycle.symm` as the constituent whose block labels
have been rotated in the same direction.  All three base block-space families use the same
coordinates, so the retyping is the identity once the target leg is inspected. -/
noncomputable def cwBaseConstituentCycleSymmEquiv (x y z : CWBlock) : ∀ c,
    CWPartitionBlockSpace K q (cycle c)
        (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z (cycle c)) ≃ₗ[K]
      CWPartitionBlockSpace K q c
        (ofLegs (V := fun _ : Leg ↦ CWBlock) y z x c) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

/-- Permuting one pure base-block tensor by `cycle.symm` rotates its three coordinate vectors in
the opposite direction to `cycle`. -/
private theorem map_cwBaseConstituentCycleSymmEquiv_pure (x y z : CWBlock)
    (vx : CWBlockIndex q x → K) (vy : CWBlockIndex q y → K)
    (vz : CWBlockIndex q z → K) :
    map (fun c ↦ (cwBaseConstituentCycleSymmEquiv K q x y z c).toLinearMap)
        (Tensor.permute cycle.symm (pure (K := K)
          (ofLegs (V := fun c ↦ CWPartitionBlockSpace K q c
            (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z c)) vx vy vz))) =
      pure (K := K)
        (ofLegs (V := fun c ↦ CWPartitionBlockSpace K q c
          (ofLegs (V := fun _ : Leg ↦ CWBlock) y z x c)) vy vz vx) := by
  rw [Tensor.permute_pure, Tensor.map_pure]
  congr 1
  funext c
  cases c <;> rfl

/-- Every supported base CW constituent is invariant under the inverse cyclic symmetry, with its
three block labels and coordinate spaces rotated accordingly.

This is the third instance of the rotation pattern of `cwConstituentOfBlocks_cycle` and
`cwConstituentOfBlocks_swap`; it is the one the zero-`X` orientation needs.

Proof sketch: the support premise leaves only the three corner and three middle constituents; for
each, expand its defining pure tensor or finite diagonal sum and apply the preceding pure-term
identity. -/
theorem cwConstituentOfBlocks_cycleSymm (x y z : CWBlock)
    (hs : ofLegs (V := fun _ : Leg ↦ CWBlock) x y z ∈ cwBlockSupport) :
    map (fun c ↦ (cwBaseConstituentCycleSymmEquiv K q x y z c).toLinearMap)
        (Tensor.permute cycle.symm (cwConstituentOfBlocks K q x y z)) =
      cwConstituentOfBlocks K q y z x := by
  cases x <;> cases y <;> cases z
  all_goals simp [cwBlockSupport, cw200, cw020, cw002, cw011, cw101, cw110,
    cwBlockAddress, ofLegs_eq_ofLegs_iff] at hs
  all_goals simp only [cwConstituentOfBlocks, map_sum]
  all_goals simp_rw [map_cwBaseConstituentCycleSymmEquiv_pure]

/-! ## Transporting a committed base certificate into a rotated frame -/

/-- Transport a zero-`Z` base certificate onto the `cycle`-rotated constituent whose labels rotate
onto it.  Used for the zero-`Y` family, where `zeroOrientation .Y = cycle`. -/
noncomputable def cwRotatedBaseOfCycle (x y z : CWBlock)
    (hs : ofLegs (V := fun _ : Leg ↦ CWBlock) x y z ∈ cwBlockSupport) {d : ℕ}
    (C : OneSliceRestriction (cwConstituentOfBlocks K q z x y) d) :
    OneSliceRestriction
      (Tensor.permute (K := K) cycle
        (cwPartitionConstituent K q (ofLegs x y z))) d :=
  (C.precompose (fun c ↦ (cwBaseConstituentCycleEquiv K q x y z c).toLinearMap)
      (cwConstituentOfBlocks_cycle K q x y z hs)).congrTensor
    (congrArg (fun T ↦ Tensor.permute (K := K) cycle T)
      (cwPartitionConstituent_ofLegs K q x y z).symm)

/-- Transport a zero-`Z` base certificate onto the `cycle.symm`-rotated constituent whose labels
rotate onto it.  Used for the zero-`X` family, where `zeroOrientation .X = cycle.symm`. -/
noncomputable def cwRotatedBaseOfCycleSymm (x y z : CWBlock)
    (hs : ofLegs (V := fun _ : Leg ↦ CWBlock) x y z ∈ cwBlockSupport) {d : ℕ}
    (C : OneSliceRestriction (cwConstituentOfBlocks K q y z x) d) :
    OneSliceRestriction
      (Tensor.permute (K := K) cycle.symm
        (cwPartitionConstituent K q (ofLegs x y z))) d :=
  (C.precompose (fun c ↦ (cwBaseConstituentCycleSymmEquiv K q x y z c).toLinearMap)
      (cwConstituentOfBlocks_cycleSymm K q x y z hs)).congrTensor
    (congrArg (fun T ↦ Tensor.permute (K := K) cycle.symm T)
      (cwPartitionConstituent_ofLegs K q x y z).symm)

/-- The identity rotation of a zero-`Z` base certificate: the committed certificate itself. -/
noncomputable def cwRotatedBaseOfRefl (x y z : CWBlock) {d : ℕ}
    (C : OneSliceRestriction (cwConstituentOfBlocks K q x y z) d) :
    OneSliceRestriction
      (Tensor.permute (K := K) (1 : Orientation)
        (cwPartitionConstituent K q (ofLegs x y z))) d :=
  (C.congrTensor (cwPartitionConstituent_ofLegs K q x y z).symm).ofPermuteOne

/-! ## The six new base certificates -/

section Named

private theorem mem_cwBlockSupport_cw200 : cw200 ∈ cwBlockSupport := by
  simp [cwBlockSupport]

private theorem mem_cwBlockSupport_cw020 : cw020 ∈ cwBlockSupport := by
  simp [cwBlockSupport]

private theorem mem_cwBlockSupport_cw002 : cw002 ∈ cwBlockSupport := by
  simp [cwBlockSupport]

private theorem mem_cwBlockSupport_cw011 : cw011 ∈ cwBlockSupport := by
  simp [cwBlockSupport]

private theorem mem_cwBlockSupport_cw101 : cw101 ∈ cwBlockSupport := by
  simp [cwBlockSupport]

private theorem mem_cwBlockSupport_cw110 : cw110 ∈ cwBlockSupport := by
  simp [cwBlockSupport]

/-- The zero-`X` corner `cw020`, rotated by `zeroOrientation .X = cycle.symm`, is `⟨1,1,1⟩`.
It transports the committed `cw200` certificate. -/
noncomputable def cw020ZeroXOneSliceRestriction :
    OneSliceRestriction
      (Tensor.permute (K := K) cycle.symm (cwPartitionConstituent K q cw020)) 1 :=
  cwRotatedBaseOfCycleSymm K q .zero .last .zero mem_cwBlockSupport_cw020
    (cw200OneSliceRestriction K q)

/-- The zero-`X` corner `cw002`, rotated by `zeroOrientation .X = cycle.symm`, is `⟨1,1,1⟩`.
It transports the committed `cw020` certificate. -/
noncomputable def cw002ZeroXOneSliceRestriction :
    OneSliceRestriction
      (Tensor.permute (K := K) cycle.symm (cwPartitionConstituent K q cw002)) 1 :=
  cwRotatedBaseOfCycleSymm K q .zero .zero .last mem_cwBlockSupport_cw002
    (cw020OneSliceRestriction K q)

/-- **The zero-`X` middle constituent `cw011`, rotated by `zeroOrientation .X = cycle.symm`, is
`⟨1,q,1⟩`.**  It transports the committed `cw110` certificate; this is the `X`-side analogue of the
only base constituent that carries a nontrivial matrix dimension. -/
noncomputable def cw011ZeroXOneSliceRestriction :
    OneSliceRestriction
      (Tensor.permute (K := K) cycle.symm (cwPartitionConstituent K q cw011)) q :=
  cwRotatedBaseOfCycleSymm K q .zero .middle .middle mem_cwBlockSupport_cw011
    (cw110OneSliceRestriction K q)

/-- The zero-`Y` corner `cw200`, rotated by `zeroOrientation .Y = cycle`, is `⟨1,1,1⟩`.
It transports the committed `cw020` certificate. -/
noncomputable def cw200ZeroYOneSliceRestriction :
    OneSliceRestriction
      (Tensor.permute (K := K) cycle (cwPartitionConstituent K q cw200)) 1 :=
  cwRotatedBaseOfCycle K q .last .zero .zero mem_cwBlockSupport_cw200
    (cw020OneSliceRestriction K q)

/-- The zero-`Y` corner `cw002`, rotated by `zeroOrientation .Y = cycle`, is `⟨1,1,1⟩`.
It transports the committed `cw200` certificate. -/
noncomputable def cw002ZeroYOneSliceRestriction :
    OneSliceRestriction
      (Tensor.permute (K := K) cycle (cwPartitionConstituent K q cw002)) 1 :=
  cwRotatedBaseOfCycle K q .zero .zero .last mem_cwBlockSupport_cw002
    (cw200OneSliceRestriction K q)

/-- **The zero-`Y` middle constituent `cw101`, rotated by `zeroOrientation .Y = cycle`, is
`⟨1,q,1⟩`.**  It transports the committed `cw110` certificate. -/
noncomputable def cw101ZeroYOneSliceRestriction :
    OneSliceRestriction
      (Tensor.permute (K := K) cycle (cwPartitionConstituent K q cw101)) q :=
  cwRotatedBaseOfCycle K q .middle .zero .middle mem_cwBlockSupport_cw101
    (cw110OneSliceRestriction K q)

end Named

/-! ## The leg-indexed base certificate -/

open MoreAsymmetryCompatibility in
/-- **Every supported base CW constituent whose `zero` block is `.zero`, read in the frame that
rotates `zero` onto `.Z`, has an explicit one-slice restriction with its canonical matrix
dimension.**

This is the orientation-indexed form of `cwZeroBaseOneSliceRestriction`, which it recovers verbatim
at `zero = .Z` (there `zeroOrientation .Z = 1` and `secondLiveLeg .Z = .Y`).  The zero-`X` and
zero-`Y` instances are transports of the committed zero-`Z` certificates along the base cyclic
symmetry; nothing is re-proved in coordinates.

Like the committed `cwZeroBaseOneSliceRestriction` this convenience form goes through
`Classical.choice`, so its `legMap` is opaque.  **The six certificates above are the choice-free
forms, and they are what a shared-fibre client needs**: `CTensor.SharedOneSliceFiberData`
(`MatrixMultiplication/SharedOneSliceFiber.lean`, landed by codex-2.36x in `0e56cc6`) asks each
constituent certificate for its `constituentMap .Z`, and `precompose_legMap` computes that for a
transported certificate from the committed one's map.  So the zero-`X` and zero-`Y` analogues of
`cwZeroBaseCoherentRestriction` can be assembled from this module without re-proving coherence in
either orientation. -/
noncomputable def cwZeroBaseRotatedOneSliceRestriction
    (zero : Leg) (support : cwBlockSupport) (hzero : support.1 zero = .zero) :
    OneSliceRestriction
      (Tensor.permute (K := K) (zeroOrientation zero)
        (cwSupportedConstituent K q support))
      (cwBaseConstituentDimension q support (secondLiveLeg zero)) := by
  classical
  refine Classical.choice ?_
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  cases zero
  · rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [cw200, cwBlockAddress] at hzero
    · exact ⟨cw020ZeroXOneSliceRestriction K q⟩
    · exact ⟨cw002ZeroXOneSliceRestriction K q⟩
    · exact ⟨cw011ZeroXOneSliceRestriction K q⟩
    · simp [cw101, cwBlockAddress] at hzero
    · simp [cw110, cwBlockAddress] at hzero
  · rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨cw200ZeroYOneSliceRestriction K q⟩
    · simp [cw020, cwBlockAddress] at hzero
    · exact ⟨cw002ZeroYOneSliceRestriction K q⟩
    · simp [cw011, cwBlockAddress] at hzero
    · exact ⟨cw101ZeroYOneSliceRestriction K q⟩
    · simp [cw110, cwBlockAddress] at hzero
  · rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨cwRotatedBaseOfRefl K q .last .zero .zero (cw200OneSliceRestriction K q)⟩
    · exact ⟨cwRotatedBaseOfRefl K q .zero .last .zero (cw020OneSliceRestriction K q)⟩
    · simp [cw002, cwBlockAddress] at hzero
    · simp [cw011, cwBlockAddress] at hzero
    · simp [cw101, cwBlockAddress] at hzero
    · exact ⟨cwRotatedBaseOfRefl K q .middle .middle .zero (cw110OneSliceRestriction K q)⟩

end AlgebraicComplexity.Examples
