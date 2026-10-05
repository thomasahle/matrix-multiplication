/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalStage
import AlgebraicComplexity.MatrixMultiplication.AsymmetricGlobalValue
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrization

/-!
# The six-symmetrized stage family of `[DuanWuZhou2022]` section 6

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoGlobalStage.lean` reduces
`[DuanWuZhou2022]`'s level-two endpoint `omega < 2.374631` to `DwzLevelTwoCountingStage`, whose
per-length input is `exists_value_of_repairedStage_true`'s premise

`hstage : Restricts (Tensor.power (sym_6 T) n) (indexedDirectSum fun _ : beta => leaf)`.

`Tensor/PartitionedSymmetrization.lean` supplies the structural half: `sym_6` of a partitioned
realization is the realization of a six-orientation partition certificate, so a positive power of
it is a legitimate restriction target.  This module joins that bridge to `[DuanWuZhou2022]`'s
section 6 assembly and to the level-two endpoint.

## What is proved here

* `restricts_power_symSix_to_repairedRestrictedSplittingDirectSum` --- the bridge composed with
  `AsymmetricGlobal.Tensor.Restricts.partitionedYZCompatibilityCleanup_to_repairedRestrictedSplittingDirectSum`.
  That engine's target is already a *constant* leaf family, so its output has exactly `hstage`'s
  shape.  Every one of its combinatorial premises --- `X`-isolation, the two compatibility
  soundness predicates, the batch surjection, the factorwise leaf restrictions, the Hole-Lemma
  budget --- is reproduced verbatim as a named hypothesis and none is discharged.
* `dwzLevelTwoCountingStage_of_stageFamily` --- one stage per word length `n + 1` assembles into
  `DwzLevelTwoCountingStage`.  No cutoff is chosen: `n := cutoff + 1` clears every cutoff.
* `omega_lt_2374631_of_dwz63StageFamily` --- the endpoint from the three lane deliverables alone
  (tensor-side stage family, count-side copy-count estimate, leaf-side weight and value rate).
  The rank budget is already discharged upstream by `dwz63_asymptoticRank_symSix_le`.
* `dwz63SymSixPartition`, `card_dwz63SymSixPartition_support` (`= 15 ^ 6 = 11390625`),
  `dwz63_restricts_power_symSix` (no hypotheses), `dwz63_stage_of_partitionedStage`.

## Why the six orientations must be hashed jointly

Symmetrizing a stage on the *plain* power `T^{tensor N}` also produces a legitimate `hstage`, and
it is much cheaper: `Isomorphic.external_indexedDirectSum` turns `sym_6` of a constant direct sum
into a constant direct sum over the sixth power of the index.  But its copy count is the product of
six *independent* retained counts, hence the product of six per-orientation moduli, whereas
`GlobalRateData.copyRate` divides by the *single* maximum
`max(N_triple/N_X, N_alpha p_comp/N_Z)` of one joint hash.  The two agree only when every
orientation selects the same branch, which `alpha_X != alpha_Z` prevents.

The gap is not marginal.  Evaluating the committed classical Coppersmith--Winograd square endpoint
`cwSquare2375477_log_sufficient` at `tau = dwz63Tau` certifies a rate of `63.9371442`, while
`dwz63TrueGlobalRate` is `64.0000112` and the border-rank budget to beat is `64`.  The level-two
bound lives entirely inside a `1.1 * 10 ^ (-5)` window above `64`, and the symmetrized plain-power
route lands `0.063` below it.  So the explicit six-orientation construction is necessary, not
merely convenient.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

namespace PartitionedTensor
/-! ## The `[DuanWuZhou2022]` section 6 assembly, applied to the six-orientation partition -/

section Repaired

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {A' : Leg → Type w} [∀ c, Fintype (A' c)] [∀ c, DecidableEq (A' c)]
variable {V' : ∀ c, A' c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V' c a)] [∀ c a, Module K (V' c a)]
variable {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {W : ∀ c, B c → Type (max u v)}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-- **`[DuanWuZhou2022]` section 6's `hstage`, for one word length, from the laser-method
premises.**

`R` is the ambient partition retained by asymmetric hashing --- any partition the six-orientation
positive power restricts onto, which is what a marked two-leg hashing seed produces.  Everything
after that is the committed generic pipeline: the two compatibility zero-outs, the batching of the
retained addresses, and the batched Hole Lemma.  Its premises are reproduced here verbatim and
none of them is discharged: they are the count-side lane's obligation at section 6.3's parameters.

What *is* discharged is the step that had no proof anywhere in the repository: that `sym₆` of a
partitioned realization is itself the realization of a partition, so that a single joint hash over
all six orientations is expressible at all. -/
theorem restricts_power_symSix_to_repairedRestrictedSplittingDirectSum
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (R : PartitionedTensor (K := K) (A := A') V')
    (hselect : Restricts (P.symSixPartition.positivePower n).realize R.realize)
    (hX : Set.InjOn (fun address : BlockAddress A' ↦ address .X) R.support)
    (compatibleY : A' .Y → BlockAddress A' → Prop)
    (hsoundY : IsCompatibilitySound R.support .Y compatibleY)
    (compatibleZ : A' .Z → BlockAddress A' → Prop)
    (hsoundZ : IsCompatibilitySound
      (compatibilityIsolatedSupport R.support .Y compatibleY) .Z compatibleZ)
    (Q : PartitionedTensor (K := K) (A := B) W) (m : ℕ) (α : B Leg.Z → ℕ)
    {β : Type*} [Fintype β] [DecidableEq β]
    (batch : (compatibilityIsolatedSupport
        (compatibilityIsolatedSupport R.support .Y compatibleY) .Z compatibleZ) → β)
    (hbatch : Function.Surjective batch)
    (holes : (compatibilityIsolatedSupport
        (compatibilityIsolatedSupport R.support .Y compatibleY) .Z compatibleZ) →
      Finset (AvailableWord (B Leg.Z) m α))
    (hleaf : ∀ address : compatibilityIsolatedSupport
        (compatibilityIsolatedSupport R.support .Y compatibleY) .Z compatibleZ,
      Restricts (R.constituent address.1)
        ((Q.restrictedSplittingPower m (SplitRestriction.ofLeg Leg.Z α)).holeSelect Leg.Z
          fun word ↦ word ∈ (holes address).image Subtype.val).realize)
    (hbudget : ∀ b : β,
      Fintype.card (AvailableWord (B Leg.Z) m α) *
          ∏ a : {a // batch a = b}, (holes a.1).card <
        Fintype.card (AvailableWord (B Leg.Z) m α) ^ Fintype.card {a // batch a = b}) :
    Restricts (Tensor.power (symSix K P.realize) (n + 1))
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K (PositivePowerBlockSpace K W m))
        fun _ ↦ (Q.restrictedSplittingPower m (SplitRestriction.ofLeg Leg.Z α)).realize) :=
  restricts_power_symSix_of_partitionedStage P n
    (hselect.trans
      (AsymmetricGlobal.Tensor.Restricts.partitionedYZCompatibilityCleanup_to_repairedRestrictedSplittingDirectSum
        R hX compatibleY hsoundY compatibleZ hsoundZ Q m α batch hbatch holes hleaf hbudget))

end Repaired


end PartitionedTensor

end AlgebraicComplexity.Tensor


namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-! ## Stage B: the family at arbitrarily large word lengths -/

/-- **The count-side residual from a family of repaired stages.**

`DwzLevelTwoCountingStage` asks for stages at arbitrarily large word lengths.  This packages one
stage per length `m + 1` --- the shape `restricts_power_symSixPartition` produces, since a positive
power of length `m` realizes the `(m+1)`-st tensor power --- into that statement.  Every numerical
obligation is a named hypothesis:

* `hcount` is the count-side lane's copy-count estimate, at the *true* rate and with the
  subexponential loss `loss` on the supplier's side;
* `hleaf` / `hvalue` are the leaf lane's `tau`-weight and its value rate;
* `hstage` is the tensor-side construction of `[DuanWuZhou2022]` section 6.

No relation among the three is assumed, and no cutoff is chosen: `n := cutoff + 1` clears every
cutoff, which is why the family is indexed by all of `ℕ`. -/
theorem dwzLevelTwoCountingStage_of_stageFamily
    {F : Type u} [Field F] {V : Leg → Type v}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)] {T : Tensor3 F V}
    {W : ℕ → Leg → Type v}
    [∀ m c, AddCommMonoid (W m c)] [∀ m c, Module F (W m c)]
    {β : ℕ → Type v} [∀ m, Fintype (β m)] [∀ m, DecidableEq (β m)]
    (leaf : ∀ m, Tensor3 F (W m)) (leafValue loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hstage : ∀ m : ℕ, Restricts (Tensor.power (symSix F T) (m + 1))
      (Tensor.indexedDirectSum (V := fun _ : β m ↦ W m) fun _ ↦ leaf m))
    (hleaf : ∀ m : ℕ, HasTauWeight F (leaf m) dwz63Tau (leafValue m))
    (hleafValue : ∀ m : ℕ, 0 < leafValue m)
    (hcards : ∀ m : ℕ, 0 < Fintype.card (β m))
    (hcount : ∀ m : ℕ,
      dwz63TrueCopyRate ^ (6 * (m + 1)) ≤ loss (m + 1) * (Fintype.card (β m) : ℝ))
    (hvalue : ∀ m : ℕ, Real.exp dwz63LogVal ^ (6 * (m + 1)) ≤ leafValue m) :
    DwzLevelTwoCountingStage T := by
  refine ⟨loss, hloss, fun cutoff ↦ ⟨cutoff + 1, Nat.le_succ cutoff, Nat.succ_pos cutoff, ?_⟩⟩
  exact exists_value_of_repairedStage_true (cutoff + 1) (hstage cutoff) (hleaf cutoff)
    (hleafValue cutoff) (hcards cutoff) (hcount cutoff) (hvalue cutoff)

/-! ## Stage C: the level-two endpoint from a stage family at the level-two source -/

/-- **`omega < 2.374631` from a six-symmetrized stage family at `[DuanWuZhou2022]`'s own level-two
source.**

The rank budget is already discharged upstream (`dwz63_asymptoticRank_symSix_le`), so the only
inputs are the three lane deliverables: the tensor-side stage family `hstage`, the count-side
estimate `hcount`, and the leaf lane's `hleaf` / `hvalue`.  Nothing else is assumed. -/
theorem omega_lt_2374631_of_dwz63StageFamily
    {F : Type u} [Field F]
    {W : ℕ → Leg → Type u}
    [∀ m c, AddCommMonoid (W m c)] [∀ m c, Module F (W m c)]
    {β : ℕ → Type u} [∀ m, Fintype (β m)] [∀ m, DecidableEq (β m)]
    (leaf : ∀ m, Tensor3 F (W m)) (leafValue loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hstage : ∀ m : ℕ, Restricts (Tensor.power (symSix F (dwz63Source F)) (m + 1))
      (Tensor.indexedDirectSum (V := fun _ : β m ↦ W m) fun _ ↦ leaf m))
    (hleaf : ∀ m : ℕ, HasTauWeight F (leaf m) dwz63Tau (leafValue m))
    (hleafValue : ∀ m : ℕ, 0 < leafValue m)
    (hcards : ∀ m : ℕ, 0 < Fintype.card (β m))
    (hcount : ∀ m : ℕ,
      dwz63TrueCopyRate ^ (6 * (m + 1)) ≤ loss (m + 1) * (Fintype.card (β m) : ℝ))
    (hvalue : ∀ m : ℕ, Real.exp dwz63LogVal ^ (6 * (m + 1)) ≤ leafValue m) :
    omega F < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_dwz63CountingStage
    (dwzLevelTwoCountingStage_of_stageFamily leaf leafValue loss hloss hstage hleaf
      hleafValue hcards hcount hvalue)

/-! ## The level-two source as a six-orientation partition -/

/-- **The six-orientation partition certificate of `[DuanWuZhou2022]`'s level-two source.**  Its
block labels are the six-tuples of the fifteen coarse Coppersmith--Winograd square addresses, one
per leg permutation; this is the object section 6's joint hash acts on. -/
noncomputable def dwz63SymSixPartition (K : Type u) [CommRing K] :=
  (cwSquarePartitionedTensor K dwz63Q).symSixPartition

/-- **The level-two six-orientation partition has `15 ^ 6 = 11390625` blocks.**  The fifteen
coarse Coppersmith--Winograd square addresses enter once per leg permutation, which is exactly the
six-fold index `[DuanWuZhou2022]` section 6's joint hash ranges over. -/
theorem card_dwz63SymSixPartition_support (K : Type u) [CommRing K] :
    (dwz63SymSixPartition K).support.card = 11390625 := by
  rw [dwz63SymSixPartition, PartitionedTensor.card_symSixPartition_support,
    cwSquarePartitionedTensor_support, card_cwSquareSupport]
  norm_num

/-- **The level-two `sym₆` stage bridge.**  Every tensor power of `sym₆` of the level-two source
restricts onto the realization of the positive power of its six-orientation partition, with no
hypothesis whatsoever.  This is the entry point of section 6's construction. -/
theorem dwz63_restricts_power_symSix (K : Type u) [CommRing K] (n : ℕ) :
    Restricts (Tensor.power (symSix K (dwz63Source K)) (n + 1))
      ((dwz63SymSixPartition K).positivePower n).realize :=
  PartitionedTensor.restricts_power_symSixPartition (cwSquarePartitionedTensor K dwz63Q) n

/-- **The level-two tensor-side stage, for one word length, from a partitioned stage.**  Together
with `dwzLevelTwoCountingStage_of_stageFamily` this is the whole tensor-side interface: a client
owes exactly one restriction of the six-orientation positive power onto a constant family of
leaves, per word length. -/
theorem dwz63_stage_of_partitionedStage
    {F : Type u} [Field F] (n : ℕ)
    {W : Leg → Type u} [∀ c, AddCommMonoid (W c)] [∀ c, Module F (W c)]
    {leaf : Tensor3 F W} {β : Type u} [Fintype β] [DecidableEq β]
    (hstage : Restricts ((dwz63SymSixPartition F).positivePower n).realize
      (Tensor.indexedDirectSum (V := fun _ : β ↦ W) fun _ ↦ leaf)) :
    Restricts (Tensor.power (symSix F (dwz63Source F)) (n + 1))
      (Tensor.indexedDirectSum (V := fun _ : β ↦ W) fun _ ↦ leaf) :=
  (dwz63_restricts_power_symSix F n).trans hstage

end AlgebraicComplexity.Examples
