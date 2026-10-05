/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradPartitionDataCore

/-!
# Cyclic and `Y`/`Z` symmetry of the base CW constituents

The base half of `Examples/CoppersmithWinogradSquareSymmetry.lean`, split off so that clients
which only need the symmetry of the *base* Coppersmith--Winograd constituents do not import the
squared tensor.  The square coarsening lifts, the eight raw exceptional identities and the two
main theorems `cwSquareConstituent_211_cycle` / `cwSquareConstituent_121_cycle` live in
`CoppersmithWinogradSquareSymmetry.lean`, which imports this file and re-exports it; no public
name and no import path changed when the two were separated.

The separation is an import-cost boundary, and a large one.  `CoppersmithWinogradSquareSymmetry`
reaches the whole `CoppersmithWinograd112` cone — the partitioned-value, entropy and asymptotics
layers, and through them `Mathlib.Analysis.SpecialFunctions.Pow.Real`,
`Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` and the `PiTensorProduct` basis theory.  None of
that is reachable from the base constituents, whose entire closure is
`CoppersmithWinogradPartitionDataCore` and the four Mathlib leaves below it.

This file carries:

* `cwBaseConstituentCycleEquiv` and `cwBaseConstituentSwapEquiv`, the retypings that identify a
  permuted base block space with the base block space of the permuted address;
* `cwConstituentOfBlocks_cycle` and `cwConstituentOfBlocks_swap`, saying that every *supported*
  base constituent is carried onto the constituent with its labels rotated, resp. with its `Y` and
  `Z` labels exchanged.

Both theorems are proved by exhausting the six supported block addresses and transporting each
defining pure term through the explicit equivalence.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## Symmetry of the six base constituents -/

/-- Retype a cyclically permuted base CW constituent as the constituent whose block labels have
been cycled in the same way.  All three base block-space families use the same coordinates, so
the retyping is the identity after inspecting the target leg. -/
noncomputable def cwBaseConstituentCycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) (x y z : CWBlock) : ∀ c,
    CWPartitionBlockSpace K q (cycle.symm c)
        (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z (cycle.symm c)) ≃ₗ[K]
      CWPartitionBlockSpace K q c
        (ofLegs (V := fun _ : Leg ↦ CWBlock) z x y c) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

/-- A cyclic leg permutation sends one pure base-block tensor to the pure tensor with coordinate
vectors rotated in the same order. -/
private theorem map_cwBaseConstituentCycleEquiv_pure
    (K : Type u) [CommRing K] (q : ℕ) (x y z : CWBlock)
    (vx : CWBlockIndex q x → K) (vy : CWBlockIndex q y → K)
    (vz : CWBlockIndex q z → K) :
    map (fun c ↦ (cwBaseConstituentCycleEquiv K q x y z c).toLinearMap)
        (Tensor.permute cycle (pure (K := K)
          (ofLegs (V := fun c ↦ CWPartitionBlockSpace K q c
            (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z c)) vx vy vz))) =
      pure (K := K)
        (ofLegs (V := fun c ↦ CWPartitionBlockSpace K q c
          (ofLegs (V := fun _ : Leg ↦ CWBlock) z x y c)) vz vx vy) := by
  rw [Tensor.permute_pure, Tensor.map_pure]
  congr 1
  funext c
  cases c <;> rfl

/-- Every supported base CW constituent is invariant under the cyclic symmetry, with its three
block labels and coordinate spaces rotated accordingly.

Proof sketch: the support premise leaves only the three corner and three middle constituents.
For each, expand its defining pure tensor or finite diagonal sum and apply the preceding pure-term
identity. -/
theorem cwConstituentOfBlocks_cycle
    (K : Type u) [CommRing K] (q : ℕ) (x y z : CWBlock)
    (hs : ofLegs (V := fun _ : Leg ↦ CWBlock) x y z ∈ cwBlockSupport) :
    map (fun c ↦ (cwBaseConstituentCycleEquiv K q x y z c).toLinearMap)
        (Tensor.permute cycle (cwConstituentOfBlocks K q x y z)) =
      cwConstituentOfBlocks K q z x y := by
  cases x <;> cases y <;> cases z
  all_goals simp [cwBlockSupport, cw200, cw020, cw002, cw011, cw101, cw110,
    cwBlockAddress, ofLegs_eq_ofLegs_iff] at hs
  all_goals simp only [cwConstituentOfBlocks, map_sum]
  all_goals simp_rw [map_cwBaseConstituentCycleEquiv_pure]

/-- Retype the base CW block spaces after interchanging the `Y` and `Z` tensor legs. -/
noncomputable def cwBaseConstituentSwapEquiv
    (K : Type u) [CommRing K] (q : ℕ) (x y z : CWBlock) : ∀ c,
    CWPartitionBlockSpace K q (xzy.symm c)
        (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z (xzy.symm c)) ≃ₗ[K]
      CWPartitionBlockSpace K q c
        (ofLegs (V := fun _ : Leg ↦ CWBlock) x z y c) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

/-- Swapping the last two legs of a pure base-block tensor swaps its last two coordinate
vectors. -/
private theorem map_cwBaseConstituentSwapEquiv_pure
    (K : Type u) [CommRing K] (q : ℕ) (x y z : CWBlock)
    (vx : CWBlockIndex q x → K) (vy : CWBlockIndex q y → K)
    (vz : CWBlockIndex q z → K) :
    map (fun c ↦ (cwBaseConstituentSwapEquiv K q x y z c).toLinearMap)
        (Tensor.permute xzy (pure (K := K)
          (ofLegs (V := fun c ↦ CWPartitionBlockSpace K q c
            (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z c)) vx vy vz))) =
      pure (K := K)
        (ofLegs (V := fun c ↦ CWPartitionBlockSpace K q c
          (ofLegs (V := fun _ : Leg ↦ CWBlock) x z y c)) vx vz vy) := by
  rw [Tensor.permute_pure, Tensor.map_pure]
  congr 1
  funext c
  cases c <;> rfl

/-- Every supported base CW constituent is invariant under swapping the `Y` and `Z` roles, with
the block labels and coordinate spaces swapped as well.

Proof sketch: reduce the support premise to the same six constituents as in the cyclic theorem,
then transport every pure defining term through the explicit swap equivalence. -/
theorem cwConstituentOfBlocks_swap
    (K : Type u) [CommRing K] (q : ℕ) (x y z : CWBlock)
    (hs : ofLegs (V := fun _ : Leg ↦ CWBlock) x y z ∈ cwBlockSupport) :
    map (fun c ↦ (cwBaseConstituentSwapEquiv K q x y z c).toLinearMap)
        (Tensor.permute xzy (cwConstituentOfBlocks K q x y z)) =
      cwConstituentOfBlocks K q x z y := by
  cases x <;> cases y <;> cases z
  all_goals simp [cwBlockSupport, cw200, cw020, cw002, cw011, cw101, cw110,
    cwBlockAddress, ofLegs_eq_ofLegs_iff] at hs
  all_goals simp only [cwConstituentOfBlocks, map_sum]
  all_goals simp_rw [map_cwBaseConstituentSwapEquiv_pure]

end AlgebraicComplexity.Examples
