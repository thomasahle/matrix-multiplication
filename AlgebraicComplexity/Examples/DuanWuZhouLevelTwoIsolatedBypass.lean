/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStageFamily
import AlgebraicComplexity.MatrixMultiplication.IndexedTauWeight
import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingValue

/-!
# The level-two endpoint from isolated whole constituents, with no hole repair

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]`'s section 6 assembly, as committed
in `AsymmetricGlobalValue.lean`, ends by *repairing* broken copies of one common leaf: its `hleaf`
asks each retained constituent to restrict **onto** a restricted-splitting power.  At the level-two
source that direction is unavailable: a retained constituent of the six-orientation power is a
single word block --- an external product of `6 n` oriented coarse constituents --- while a
restricted-splitting power of the coarse square is a direct sum over many words, and
`Tensor.Restricts.partitionedConstituent` runs the other way.  The engine was built for the
two-level localized sources where a hashed outer block genuinely contains an inner power.

None of that is needed.  `DwzLevelTwoCountingStage` asks only for a `tau`-weight on
`Tensor.power (sym_6 T) n`, and weights are **additive** over direct sums.  So a cleanup that
retains *whole constituents* --- the shape
`Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum` already produces, before
any batching or hole repair --- suffices on its own:

* every retained constituent carries the leaf rate (its oriented coarse letters are
  `dwz63Alpha`-typical, so its weight is the one-period base raised to the scale);
* `HasTauWeight.indexedDirectSum_of_forall` adds those weights, giving
  `card(isolated) * (leaf rate)`;
* `HasTauWeight.of_restricts` transports the total to the `sym_6` power.

The retained copy count is `Fintype.card` of the isolated support directly.  There is no `Q`, no
`m`, no `alpha` split, no hole family, no batch surjection and no Hole-Lemma budget.

## What still has to be supplied, and by whom

* `hsum` --- the hashing lane: one restriction of the `sym_6` power onto the direct sum of the
  isolated constituents.  Composing `restricts_power_symSixPartition` with an `X`-isolation and
  the two compatibility zero-outs produces exactly this shape.
* `hconstituent` --- the values lane: every retained constituent is worth at least `w i`.
  `hasTauWeight_symSixPartition_constituent` below reduces one constituent to the six oriented
  coarse weights, and `hasTauWeight_wordTensor` together with
  `positiveSupportWordWeight_eq_prod_pow` turns a `dwz63Alpha`-typical word into the one-period
  base raised to the scale.
* `hcount` --- the counting lane.

## Orientation invariance is proved, not assumed

A letter of the six-orientation partition is an external product of six *permuted* coarse
constituents, and `PartitionedTensor.permute_constituent` presents each of them as a leg
permutation followed by a dependent cast of the block spaces.  `HasTauWeight.permute` handles the
first and `HasTauWeight.map_linearEquiv` the second, so
`hasTauWeight_permute_partitionedConstituent` needs no hypothesis: a coarse weight is worth the
same in every orientation.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

/-! ## Orientation invariance for partitioned constituents -/

section Orientation

variable {K : Type u} [Field K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **A coarse constituent is worth the same in every orientation.**

`PartitionedTensor.permute_constituent` presents a permuted constituent as `Tensor.permute` of the
source constituent followed by a dependent cast of the three block spaces; `HasTauWeight.permute`
handles the permutation and `HasTauWeight.map_linearEquiv` the cast. -/
theorem hasTauWeight_permute_partitionedConstituent
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation) {τ value : ℝ}
    (s : BlockAddress (PermutedBlockIndex e A))
    (h : HasTauWeight K (P.constituent ((permuteBlockAddress e).symm s)) τ value) :
    HasTauWeight K ((P.permute e).constituent s) τ value := by
  rw [PartitionedTensor.permute_constituent]
  exact HasTauWeight.map_linearEquiv
    (fun c ↦ permuteBlockSpaceCast (K := K) (V := V) e s c) (h.permute e)

end Orientation

/-! ## One letter of the six-orientation partition -/

section SymSixConstituent

variable {K : Type u} [Field K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- An external constituent is the external product of the two factor constituents, so its weight
is the product of theirs.  This is definitional on the tensor side. -/
theorem hasTauWeight_external_partitionedConstituent
    {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
    {W : ∀ c, B c → Type (max u v)}
    [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) {τ a b : ℝ}
    (q : BlockAddress (ProductBlockIndex A B))
    (hP : HasTauWeight K (P.constituent fun c ↦ (q c).1) τ a)
    (hQ : HasTauWeight K (Q.constituent fun c ↦ (q c).2) τ b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasTauWeight K ((P.external Q).constituent q) τ (a * b) :=
  HasTauWeight.external hP hQ ha hb

end SymSixConstituent

end AlgebraicComplexity

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v w


/-! ## The decoupled form -/

/-- **The rate arithmetic of the bypass, with no tensor types.**  Splitting the global rate into
its copy and value factors, a copy-count estimate and a per-constituent weight multiply into the
endpoint's inequality. -/
theorem dwz63_globalRate_le_of_count_value {count weight lossN : ℝ} {n : ℕ}
    (hcount : dwz63TrueCopyRate ^ (6 * n) ≤ lossN * count)
    (hvalue : Real.exp dwz63LogVal ^ (6 * n) ≤ weight) :
    dwz63TrueGlobalRate ^ (6 * n) ≤ lossN * (count * weight) := by
  have hexpand : dwz63TrueGlobalRate ^ (6 * n) =
      dwz63TrueCopyRate ^ (6 * n) * Real.exp dwz63LogVal ^ (6 * n) := by
    rw [dwz63TrueGlobalRate, mul_pow]
  rw [hexpand]
  calc dwz63TrueCopyRate ^ (6 * n) * Real.exp dwz63LogVal ^ (6 * n)
      ≤ lossN * count * weight :=
        mul_le_mul hcount hvalue (pow_pos (Real.exp_pos _) _).le
          ((pow_pos dwz63TrueCopyRate_pos _).le.trans hcount)
    _ = lossN * (count * weight) := by ring

/-- **The bypass, decoupled from the shape of the restriction target.**

The target `S j` is opaque and its weight is supplied directly, so a client wiring a concrete
hashing result in never triggers higher-order unification against the block spaces of a
six-orientation positive power --- which is a genuine elaboration hazard, since those spaces
unfold to a six-fold `ProductBlockSpace` under a `PositivePowerBlockSpace`.

`dwzLevelTwoCountingStage_of_isolatedSum` is the special case where `S j` is the indexed direct sum
of the isolated constituents and the weight comes from
`HasTauWeight.indexedDirectSum_of_forall`. -/
theorem dwzLevelTwoCountingStage_of_weightedRestriction
    {K : Type u} [Field K] {Wsp : ℕ → Leg → Type v}
    [∀ j c, AddCommMonoid (Wsp j c)] [∀ j c, Module K (Wsp j c)]
    (index : ℕ → ℕ) (S : ∀ j : ℕ, Tensor3 K (Wsp j)) (value loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ index j ∧ 0 < index j)
    (hsum : ∀ j : ℕ, Restricts (Tensor.power (symSix K (dwz63Source K)) (index j)) (S j))
    (hweight : ∀ j : ℕ, HasTauWeight K (S j) dwz63Tau (value j))
    (hpos : ∀ j : ℕ, 0 < value j)
    (hrate : ∀ j : ℕ, dwz63TrueGlobalRate ^ (6 * index j) ≤ loss (index j) * value j) :
    DwzLevelTwoCountingStage (dwz63Source K) := by
  refine ⟨loss, hloss, fun cutoff ↦ ?_⟩
  obtain ⟨j, hj, hjpos⟩ := hcofinal cutoff
  exact ⟨index j, hj, hjpos, value j, hpos j,
    HasTauWeight.of_restricts (hsum j) (hweight j), hrate j⟩

/-- **`omega < 2.374631` in the decoupled form.** -/
theorem omega_lt_2374631_of_weightedRestriction
    {K : Type u} [Field K] {Wsp : ℕ → Leg → Type v}
    [∀ j c, AddCommMonoid (Wsp j c)] [∀ j c, Module K (Wsp j c)]
    (index : ℕ → ℕ) (S : ∀ j : ℕ, Tensor3 K (Wsp j)) (value loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ index j ∧ 0 < index j)
    (hsum : ∀ j : ℕ, Restricts (Tensor.power (symSix K (dwz63Source K)) (index j)) (S j))
    (hweight : ∀ j : ℕ, HasTauWeight K (S j) dwz63Tau (value j))
    (hpos : ∀ j : ℕ, 0 < value j)
    (hrate : ∀ j : ℕ, dwz63TrueGlobalRate ^ (6 * index j) ≤ loss (index j) * value j) :
    omega K < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_dwz63CountingStage
    (dwzLevelTwoCountingStage_of_weightedRestriction index S value loss hloss hcofinal hsum
      hweight hpos hrate)

/-! ## The bypass -/

/-- **The count-side residual from isolated whole constituents.**

No hole repair, no batching, no common leaf: the retained constituents differ, their weights add
by `HasTauWeight.indexedDirectSum_of_forall`, and the copy count is the cardinality of the isolated
support itself. -/
theorem dwzLevelTwoCountingStage_of_isolatedSum
    {K : Type u} [Field K]
    {Iso : ℕ → Type w} [∀ i, Fintype (Iso i)] [∀ i, DecidableEq (Iso i)]
    {U : ∀ i, Iso i → Leg → Type v}
    [∀ i a c, AddCommMonoid (U i a c)] [∀ i a c, Module K (U i a c)]
    (index : ℕ → ℕ) (retained : ∀ i, ∀ a : Iso i, Tensor3 K (U i a))
    (w loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hcofinal : ∀ cutoff : ℕ, ∃ i : ℕ, cutoff ≤ index i ∧ 0 < index i)
    (hsum : ∀ i : ℕ, Restricts (Tensor.power (symSix K (dwz63Source K)) (index i))
      (Tensor.indexedDirectSum fun a : Iso i ↦ retained i a))
    (hconstituent : ∀ (i : ℕ) (a : Iso i), HasTauWeight K (retained i a) dwz63Tau (w i))
    (hwpos : ∀ i : ℕ, 0 < w i)
    (hcards : ∀ i : ℕ, 0 < Fintype.card (Iso i))
    (hcount : ∀ i : ℕ,
      dwz63TrueCopyRate ^ (6 * index i) ≤ loss (index i) * (Fintype.card (Iso i) : ℝ))
    (hvalue : ∀ i : ℕ, Real.exp dwz63LogVal ^ (6 * index i) ≤ w i) :
    DwzLevelTwoCountingStage (dwz63Source K) := by
  refine ⟨loss, hloss, fun cutoff ↦ ?_⟩
  obtain ⟨i, hi, hpos⟩ := hcofinal cutoff
  have hcardPos : (0 : ℝ) < (Fintype.card (Iso i) : ℝ) := by exact_mod_cast hcards i
  refine ⟨index i, hi, hpos, (Fintype.card (Iso i) : ℝ) * w i,
    mul_pos hcardPos (hwpos i), ?_, ?_⟩
  · exact HasTauWeight.of_restricts (hsum i)
      (HasTauWeight.indexedDirectSum_of_forall (hconstituent i))
  · have hexpand : dwz63TrueGlobalRate ^ (6 * index i) =
        dwz63TrueCopyRate ^ (6 * index i) * Real.exp dwz63LogVal ^ (6 * index i) := by
      rw [dwz63TrueGlobalRate, mul_pow]
    rw [hexpand]
    calc dwz63TrueCopyRate ^ (6 * index i) * Real.exp dwz63LogVal ^ (6 * index i)
        ≤ loss (index i) * (Fintype.card (Iso i) : ℝ) * w i :=
          mul_le_mul (hcount i) (hvalue i) (pow_pos (Real.exp_pos _) _).le
            ((pow_pos dwz63TrueCopyRate_pos _).le.trans (hcount i))
      _ = loss (index i) * ((Fintype.card (Iso i) : ℝ) * w i) := by ring

/-- **`omega < 2.374631` from isolated whole constituents.**

The level-two endpoint with the hole-repair branch of the section 6 assembly bypassed entirely.
Three lane inputs remain: the isolation restriction, the per-constituent weight, and the copy
count. -/
theorem omega_lt_2374631_of_dwz63IsolatedSum
    {K : Type u} [Field K]
    {Iso : ℕ → Type w} [∀ i, Fintype (Iso i)] [∀ i, DecidableEq (Iso i)]
    {U : ∀ i, Iso i → Leg → Type v}
    [∀ i a c, AddCommMonoid (U i a c)] [∀ i a c, Module K (U i a c)]
    (index : ℕ → ℕ) (retained : ∀ i, ∀ a : Iso i, Tensor3 K (U i a))
    (w loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hcofinal : ∀ cutoff : ℕ, ∃ i : ℕ, cutoff ≤ index i ∧ 0 < index i)
    (hsum : ∀ i : ℕ, Restricts (Tensor.power (symSix K (dwz63Source K)) (index i))
      (Tensor.indexedDirectSum fun a : Iso i ↦ retained i a))
    (hconstituent : ∀ (i : ℕ) (a : Iso i), HasTauWeight K (retained i a) dwz63Tau (w i))
    (hwpos : ∀ i : ℕ, 0 < w i)
    (hcards : ∀ i : ℕ, 0 < Fintype.card (Iso i))
    (hcount : ∀ i : ℕ,
      dwz63TrueCopyRate ^ (6 * index i) ≤ loss (index i) * (Fintype.card (Iso i) : ℝ))
    (hvalue : ∀ i : ℕ, Real.exp dwz63LogVal ^ (6 * index i) ≤ w i) :
    omega K < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_dwz63CountingStage
    (dwzLevelTwoCountingStage_of_isolatedSum index retained w loss hloss hcofinal hsum
      hconstituent hwpos hcards hcount hvalue)

end AlgebraicComplexity.Examples
