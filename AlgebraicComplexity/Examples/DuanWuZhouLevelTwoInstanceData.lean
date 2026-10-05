/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStageFamily
import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingPower

/-!
# Section 6.3's engine data: the inner tensor, the `Z` split, and the leaf

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoStageFamily.lean` reduces
`[DuanWuZhou2022]`'s level-two endpoint to one application of
`AsymmetricGlobal.Tensor.Restricts.partitionedYZCompatibilityCleanup_to_repairedRestrictedSplittingDirectSum`
on the six-orientation partition.  That engine is parameterized by an inner partition `Q`, a
length `m`, a `Z` split `alpha`, a hole family and one restriction per retained constituent.  This
module fixes the first three at section 6.3's own parameters and names the resulting leaf, so that
the leaf lane has a typed target and the hashing lane has a typed ambient.

## The leaf is a restricted-splitting power, not a matrix-multiplication tensor

Two leaf conventions coexist in this repository and they are **not** interchangeable.

* The Coppersmith--Winograd chain (`CoppersmithWinogradChunkTypedLeaf`,
  `cw112SymmetricLeaf`, `TauValueCertificate`) restricts each retained constituent onto a
  *rectangular matrix-multiplication tensor* `<m,n,p>`.  Its value is the volume sum
  `(sum (m n p)^tau)^(1/N)`.
* `[DuanWuZhou2022]`'s engine restricts each retained constituent onto a **broken copy of a
  restricted-splitting power** `Q^{tensor (m+1)}[alphatilde]` (Definition 2.14 and Definition 5.2).
  Its value is not a volume sum: it is the inter-level interface, the *pair*
  `(V^{(6)}(T_{i,j,k}, alphatilde), alphatilde_{i,j,k})`, produced by a laser analysis one level
  down.

`dwz63LogVal` --- the committed `log alphabar_val` --- is by its own definition

`log prod_{(i,j,k)} V^{(6)}(T_{i,j,k}, alphatilde) ^ alpha(i,j,k)`,

a product over the **fifteen** coarse square components: `1` on the three corners, `(2q)^tau` on
the six `(0,1,3)`-type components, `(q^2+2)^tau` on `(2,2,0)`, the `a`-split formula on
`(0,2,2)`/`(2,0,2)`, the `b`-split formula on `(1,1,2)`, and the `lem:non-rot-values` (d) formula
on `(1,2,1)`/`(2,1,1)`.  The `(1,1,2)` analysis is therefore **one factor of fifteen**, and it
enters at section 6.3's own `b` split, not at the classical `(L,G) = (7,247)` of
`Examples/CoppersmithWinograd2375477.lean`.  So the engine leaf is not a `(1,1,2)` typed-leaf
power and must not be identified with one; `Dwz63EngineLeafValue` below states the contract that
is actually owed.

## What is fixed here

* `dwz63EngineInner` --- the engine's `Q`: the level-two source as a partition certificate,
  `cwSquarePartitionedTensor K dwz63Q`, whose realization is `dwz63Source K` by definition.
* `dwz63EngineSplitProfile` / `dwz63EngineSplit` --- the engine's `alpha`: the committed section
  6.3 `Z` marginal `dwz63AlphaZ`, scaled proportionally, restricting the `Z` leg only.
* `dwz63EngineLeafPartition` / `dwz63EngineLeaf` --- the engine's leaf and its support
  characterization.
* `dwz63_stage_of_engineData` --- the section 6 assembly instantiated at exactly this data.  Its
  surviving hypotheses are the hashing lane's (`hselect`, `hX`, `batch`, `hbudget`), the
  compatibility predicates (whose soundness
  `Tensor/PartitionedSymmetrizedCompatibility.lean` discharges) and `holes` / `hleaf`.
* `Dwz63EngineLeafValue` and `omega_lt_2374631_of_dwz63EngineData` --- the leaf lane's contract,
  and the endpoint conditional on it together with the stage family and the copy count.

Nothing here is proved about how large the isolated support is, nor about the leaf's value: those
are the counting and leaf obligations respectively.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

noncomputable section

/-! ## The engine's inner tensor -/

/-- **The engine's inner partition `Q` at section 6.3**: the level-two source, presented as the
partition certificate whose realization is `dwz63Source`. -/
noncomputable def dwz63EngineInner (K : Type u) [CommRing K] :
    PartitionedTensor (K := K) (A := fun _ : Leg ↦ Fin 5) (CWSquareBlockSpace K dwz63Q) :=
  cwSquarePartitionedTensor K dwz63Q

/-- The engine's inner partition realizes the level-two source, definitionally. -/
theorem dwz63EngineInner_realize (K : Type u) [CommRing K] :
    (dwz63EngineInner K).realize = dwz63Source K := rfl

/-- The engine's inner partition has the fifteen coarse square addresses. -/
theorem dwz63EngineInner_support_card (K : Type u) [CommRing K] :
    (dwz63EngineInner K).support.card = 15 := by
  rw [dwz63EngineInner, cwSquarePartitionedTensor_support, card_cwSquareSupport]

/-! ## The engine's `Z` split -/

/-- **The engine's `alpha` at section 6.3**: the committed `Z` marginal at proportional scale `k`.
`dwz63AlphaZ` has mass `10 ^ 8`, so the scaled profile has mass `k`. -/
def dwz63EngineSplitProfile (k : ℕ) : Fin 5 → ℕ :=
  WordType.proportionalCounts dwz63AlphaZ k

/-- **The engine's split restriction**: only the `Z` leg is constrained, by the section 6.3 `Z`
type.  This is `[DuanWuZhou2022]`'s default orientation (`X` and `Y` are used in section 7). -/
def dwz63EngineSplit (k : ℕ) : SplitRestriction (fun _ : Leg ↦ Fin 5) :=
  SplitRestriction.ofLeg Leg.Z (dwz63EngineSplitProfile k)

@[simp] theorem dwz63EngineSplit_Z (k : ℕ) :
    dwz63EngineSplit k Leg.Z = some (dwz63EngineSplitProfile k) :=
  SplitRestriction.ofLeg_self (A := fun _ : Leg ↦ Fin 5) Leg.Z (dwz63EngineSplitProfile k)

@[simp] theorem dwz63EngineSplit_X (k : ℕ) : dwz63EngineSplit k Leg.X = none :=
  SplitRestriction.ofLeg_of_ne (A := fun _ : Leg ↦ Fin 5) (dwz63EngineSplitProfile k)
    (by decide : (Leg.Z : Leg) ≠ Leg.X)

@[simp] theorem dwz63EngineSplit_Y (k : ℕ) : dwz63EngineSplit k Leg.Y = none :=
  SplitRestriction.ofLeg_of_ne (A := fun _ : Leg ↦ Fin 5) (dwz63EngineSplitProfile k)
    (by decide : (Leg.Z : Leg) ≠ Leg.Y)

/-! ## The engine's leaf -/

/-- **The engine's leaf at section 6.3**, as a partition certificate: the restricted-splitting
power `T^{tensor (m+1)}[alphatilde_Z]` of `[DuanWuZhou2022]` Definition 2.14. -/
noncomputable def dwz63EngineLeafPartition (K : Type u) [CommRing K] (m k : ℕ) :
    PartitionedTensor (K := K) (A := fun _ : Leg ↦ PositiveWord (Fin 5) m)
      (PositivePowerBlockSpace K (CWSquareBlockSpace K dwz63Q) m) :=
  (dwz63EngineInner K).restrictedSplittingPower m (dwz63EngineSplit k)

/-- **The engine's leaf**, as a tensor.  This is the object the leaf lane must weigh. -/
noncomputable def dwz63EngineLeaf (K : Type u) [CommRing K] (m k : ℕ) :=
  (dwz63EngineLeafPartition K m k).realize

/-- **Exactly which blocks the leaf keeps**: those of the ambient square power whose `Z` word has
the section 6.3 empirical type.  The `X` and `Y` words are unconstrained --- that asymmetry is the
point of the construction. -/
theorem mem_dwz63EngineLeafPartition_support
    (K : Type u) [CommRing K] (m k : ℕ)
    (address : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) m)) :
    address ∈ (dwz63EngineLeafPartition K m k).support ↔
      address ∈ ((dwz63EngineInner K).positivePower m).support ∧
        WordType.multiplicity
            (positiveWordEquiv (Fin 5) m (address Leg.Z)) = dwz63EngineSplitProfile k := by
  rw [dwz63EngineLeafPartition,
    PartitionedTensor.mem_restrictedSplittingPower_support]
  constructor
  · rintro ⟨hambient, hkeeps⟩
    exact ⟨hambient, (SplitRestriction.keeps_some_iff
      (dwz63EngineSplit_Z k) (address Leg.Z)).mp (hkeeps Leg.Z)⟩
  · rintro ⟨hambient, hZ⟩
    refine ⟨hambient, fun c ↦ ?_⟩
    match c with
    | Leg.X => exact SplitRestriction.keeps_of_none (dwz63EngineSplit_X k) _
    | Leg.Y => exact SplitRestriction.keeps_of_none (dwz63EngineSplit_Y k) _
    | Leg.Z => exact (SplitRestriction.keeps_some_iff
        (dwz63EngineSplit_Z k) (address Leg.Z)).mpr hZ

/-- The leaf is an exact restriction of the ambient square power: the split is a zero-out, not an
assumption. -/
theorem restricts_dwz63EnginePower_leaf (K : Type u) [CommRing K] (m k : ℕ) :
    Restricts ((dwz63EngineInner K).positivePower m).realize (dwz63EngineLeaf K m k) :=
  Tensor.Restricts.partitionedPositivePower_restrictedSplittingPower
    (dwz63EngineInner K) m (dwz63EngineSplit k)

/-! ## The leaf lane's contract, and the endpoint at concrete engine data -/

/-- **The contract the leaf lane owes, at the engine's own leaf.**

Not a volume sum, and not a `(1,1,2)` typed-leaf power: a `tau`-weight on the restricted-splitting
power `T^{tensor (m+1)}[alphatilde_Z]` itself, realizing the section 6.3 value rate
`alphabar_val = exp dwz63LogVal`.  By `dwz63LogVal`'s own definition that rate is the product over
the fifteen coarse square components of `V^{(6)}(T_{i,j,k}, alphatilde) ^ alpha(i,j,k)`, so
discharging this contract means bounding each of those fifteen factors --- the `(1,1,2)` chain
supplies exactly one of them. -/
def Dwz63EngineLeafValue (F : Type u) [Field F] (m k : ℕ → ℕ) (leafValue : ℕ → ℝ) : Prop :=
  ∀ j : ℕ, 0 < leafValue j ∧
    HasTauWeight F (dwz63EngineLeaf F (m j) (k j)) dwz63Tau (leafValue j) ∧
    Real.exp dwz63LogVal ^ (6 * (j + 1)) ≤ leafValue j

/-- **`omega < 2.374631` at concrete section 6.3 engine data.**

The leaf is no longer abstract: it is `dwz63EngineLeaf`, the restricted-splitting power of the
level-two source at the committed `Z` marginal.  What remains are exactly three lane contracts ---
the tensor-side stage family `hstage`, the count-side `hcards` / `hcount`, and the leaf-side
`Dwz63EngineLeafValue` --- with no hidden hypothesis and no rank obligation. -/
theorem omega_lt_2374631_of_dwz63EngineData
    {F : Type u} [Field F] (m k : ℕ → ℕ) (leafValue loss : ℕ → ℝ)
    {β : ℕ → Type u} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    (hloss : Growth.Subexponential loss)
    (hstage : ∀ j : ℕ, Restricts (Tensor.power (symSix F (dwz63Source F)) (j + 1))
      (Tensor.indexedDirectSum (V := fun _ : β j ↦ _) fun _ ↦ dwz63EngineLeaf F (m j) (k j)))
    (hleafValue : Dwz63EngineLeafValue F m k leafValue)
    (hcards : ∀ j : ℕ, 0 < Fintype.card (β j))
    (hcount : ∀ j : ℕ,
      dwz63TrueCopyRate ^ (6 * (j + 1)) ≤ loss (j + 1) * (Fintype.card (β j) : ℝ)) :
    omega F < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_dwz63StageFamily
    (fun j ↦ dwz63EngineLeaf F (m j) (k j)) leafValue loss hloss hstage
    (fun j ↦ (hleafValue j).2.1) (fun j ↦ (hleafValue j).1) hcards hcount
    (fun j ↦ (hleafValue j).2.2)

end

end AlgebraicComplexity.Examples
