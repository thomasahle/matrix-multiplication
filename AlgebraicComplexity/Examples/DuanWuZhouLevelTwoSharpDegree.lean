/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHashRetention

/-!
# The sharp leg-fiber degree of the level-two joint hash

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoHashRetention.lean` fixes
the hashing parameters at the *crude* degree `dwz63AmbientDegree n = 11390625 ^ (n+1)`, which is
correct but rate-vacuous.  `[DuanWuZhou2022]` §6.3's degree is `N_triple / N_X`, and the whole rate
gain lives in that ratio (`PREP.md` §4.3 (a)/(d)).  This module supplies the structure that ratio
needs, and re-instantiates the retention bound at any degree a client can certify.

## Which marginal each orientation's `X` leg sees

`PartitionedTensor.permute e` puts the source leg `e.symm c` at target leg `c`, so the `X` label
of a `symSixPartition` address is a six-tuple whose `i`-th entry is the source label at leg
`σᵢ.symm .X`, where `σ₁ … σ₆` are the identity, `cycle`, `cycle.symm`, `swapXY`,
`cycle.trans swapXY` and `cycle.symm.trans swapXY` in the association of
`PartitionedTensor.symSixPartition`.

`dwz63SymSixXLegSource_values` computes those six legs and they are **not six copies of the `X`
marginal**:

`X`-leg sources: `X, Z, Y, Y, X, Z`  —  `Z`-leg sources: `Z, Y, X, Z, Y, X`.

Each of the three source legs occurs exactly twice on each target leg
(`dwz63SymSix_legSource_count`), which is what one should expect: `sym₆` is the six-fold
symmetrization, so every leg of `sym₆(T)` sees every leg of `T` the same number of times.  Since
the coarse Coppersmith--Winograd square is `X`/`Y` symmetric --- `α_X·D = α_Y·D =
[12957007, 43285992, 41147194, 2585076, 24731]` while
`α_Z·D = [12598769, 44135552, 40822513, 2422306, 20860]` (`PREP.md` §6) --- the six marginals seen
by the `X` leg are four copies of `α_X` and two of `α_Z`, and the `Z` leg sees **the same
multiset**.  So `N_X` and `N_Z` of the six-orientation power have equal rate, and the two branches
of `dwz63TrueCopyRate` can differ only through the compatibility factor `ᾱ_p`.  That is a
structural fact about the six-symmetrization, not about the numbers, and it is recorded here as
`dwz63SymSix_xLegSource_multiset_eq_zLegSource_multiset`.

## The sharp degree

`dwz63SharpDegree` is `⌊N_triple / N_X⌋ + 1` for whichever pair of counts a client certifies, so
`dwz63SharpDegree_spec` is the division-free `N_triple ≤ N_X · dwz63SharpDegree`.  The counting
work --- that the typical words sharing an `X`-label word really do number at most this --- is the
method-of-types obligation of `MatrixMultiplication/CompatibilityIsolationCounting.lean`'s
`ConditionalCompetitorEncoding`, and it enters `dwz63_retained_card_lower_sharp` below as the
explicit hypothesis `hsharp`.

## What is stated but not proved

`Dwz63SharpRateStatement` is a `Prop`-valued *definition*, not a theorem: it is the exponential
form the count lane must eventually establish, namely that `log N_X − log(sharp degree)` realizes
`dwz63EntropyX` up to `o(n)`.  Naming it here fixes the interface without claiming it.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The six orientations of `symSixPartition` -/

/-- The six leg permutations of `PartitionedTensor.symSixPartition`, in its own association. -/
def dwz63SymSixOrientation : Fin 6 → Orientation
  | 0 => Equiv.refl Leg
  | 1 => cycle
  | 2 => cycle.symm
  | 3 => swapXY
  | 4 => cycle.trans swapXY
  | 5 => cycle.symm.trans swapXY

/-- The source leg that orientation `i` places at target leg `c`. -/
def dwz63SymSixLegSource (i : Fin 6) (c : Leg) : Leg :=
  (dwz63SymSixOrientation i).symm c

/-- **The six source legs seen by the `X` leg**: `X, Z, Y, Y, X, Z`. -/
theorem dwz63SymSixXLegSource_values :
    (List.finRange 6).map (fun i ↦ dwz63SymSixLegSource i .X)
      = [Leg.X, Leg.Z, Leg.Y, Leg.Y, Leg.X, Leg.Z] := by decide

/-- **The six source legs seen by the `Z` leg**: `Z, Y, X, Z, Y, X`. -/
theorem dwz63SymSixZLegSource_values :
    (List.finRange 6).map (fun i ↦ dwz63SymSixLegSource i .Z)
      = [Leg.Z, Leg.Y, Leg.X, Leg.Z, Leg.Y, Leg.X] := by decide

/-- **The six source legs seen by the `Y` leg**: `Y, X, Z, X, Z, Y`. -/
theorem dwz63SymSixYLegSource_values :
    (List.finRange 6).map (fun i ↦ dwz63SymSixLegSource i .Y)
      = [Leg.Y, Leg.X, Leg.Z, Leg.X, Leg.Z, Leg.Y] := by decide

/-- **Every target leg sees every source leg exactly twice.**  This is the structural reason the
six-orientation power's three leg marginals are all the same multiset of source marginals. -/
theorem dwz63SymSix_legSource_count (c d : Leg) :
    ((List.finRange 6).map (fun i ↦ dwz63SymSixLegSource i c)).count d = 2 := by
  revert c d; decide

/-- **The `X` and `Z` legs of the six-orientation power see the same multiset of source legs.**
Hence `N_X` and `N_Z` of that power have equal exponential rate, and the two branches of
`dwz63TrueCopyRate` separate only through the compatibility factor. -/
theorem dwz63SymSix_xLegSource_multiset_eq_zLegSource_multiset :
    (((List.finRange 6).map (fun i ↦ dwz63SymSixLegSource i .X) : List Leg) : Multiset Leg)
      = (((List.finRange 6).map (fun i ↦ dwz63SymSixLegSource i .Z) : List Leg) : Multiset Leg) := by
  decide

/-! ## The marginals seen by each leg

`dwz63AlphaX` and `dwz63AlphaZ` are committed at HEAD in
`Examples/DuanWuZhouLevelTwoGlobalStage.lean`; nothing is redefined here.  Since the coarse square
is `X`/`Y` symmetric (`α_X = α_Y`, `PREP.md` §6), the leg-source computation above says the `X` leg
of the six-orientation power sees the marginals `α_X, α_Z, α_Y, α_Y, α_X, α_Z`, i.e. **four copies
of `α_X` and two of `α_Z`**, and the `Z` leg sees `α_Z, α_Y, α_X, α_Z, α_Y, α_X`, i.e. the same
multiset. -/

/-- The source marginal that orientation `i` places at target leg `c`, as a function of the source
leg it reads.  A client supplies the three source marginals; the leg-source computation above then
determines the six factors of the leg's own marginal. -/
def dwz63LegSourceMarginal (marginal : Leg → Fin 5 → ℕ) (i : Fin 6) (c : Leg) : Fin 5 → ℕ :=
  marginal (dwz63SymSixLegSource i c)

/-- **The `X` leg of the six-orientation power reads `α_X, α_Z, α_Y, α_Y, α_X, α_Z`.**  With
`α_X = α_Y` this is four copies of the `X` marginal and two of the `Z` marginal. -/
theorem dwz63LegSourceMarginal_X (marginal : Leg → Fin 5 → ℕ) :
    dwz63LegSourceMarginal marginal 0 .X = marginal .X ∧
    dwz63LegSourceMarginal marginal 1 .X = marginal .Z ∧
    dwz63LegSourceMarginal marginal 2 .X = marginal .Y ∧
    dwz63LegSourceMarginal marginal 3 .X = marginal .Y ∧
    dwz63LegSourceMarginal marginal 4 .X = marginal .X ∧
    dwz63LegSourceMarginal marginal 5 .X = marginal .Z :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The `Z` leg of the six-orientation power reads `α_Z, α_Y, α_X, α_Z, α_Y, α_X`** --- the same
multiset as the `X` leg, so `N_X` and `N_Z` of the six-orientation power have equal rate. -/
theorem dwz63LegSourceMarginal_Z (marginal : Leg → Fin 5 → ℕ) :
    dwz63LegSourceMarginal marginal 0 .Z = marginal .Z ∧
    dwz63LegSourceMarginal marginal 1 .Z = marginal .Y ∧
    dwz63LegSourceMarginal marginal 2 .Z = marginal .X ∧
    dwz63LegSourceMarginal marginal 3 .Z = marginal .Z ∧
    dwz63LegSourceMarginal marginal 4 .Z = marginal .Y ∧
    dwz63LegSourceMarginal marginal 5 .Z = marginal .X :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The sharp degree -/

/-- **`[DuanWuZhou2022]`'s degree `N_triple / N_X`**, in the rounded-up division-free form: the
client supplies the joint typical count `jointCount` and the `X`-marginal typical count `xCount`,
and this is the smallest integer with `jointCount ≤ xCount * degree`. -/
def dwz63SharpDegree (jointCount xCount : ℕ) : ℕ := jointCount / xCount + 1

/-- **The defining inequality, division-free.** -/
theorem dwz63SharpDegree_spec (jointCount xCount : ℕ) (hx : 0 < xCount) :
    jointCount ≤ xCount * dwz63SharpDegree jointCount xCount := by
  unfold dwz63SharpDegree
  calc jointCount = xCount * (jointCount / xCount) + jointCount % xCount :=
        (Nat.div_add_mod jointCount xCount).symm
    _ ≤ xCount * (jointCount / xCount) + xCount :=
        Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt jointCount hx)) _
    _ = xCount * (jointCount / xCount + 1) := by ring

theorem dwz63SharpDegree_pos (jointCount xCount : ℕ) :
    0 < dwz63SharpDegree jointCount xCount := Nat.succ_pos _

/-! ## Retention at the sharp degree -/

/-- The Bertrand modulus at a client-supplied degree. -/
noncomputable def dwz63SharpHashModulus (degree : ℕ) : ℕ :=
  PrimeFieldSizing.modulus 15625 (8 * degree)

instance dwz63SharpHashModulus_fact_prime (degree : ℕ) :
    Fact (Nat.Prime (dwz63SharpHashModulus degree)) :=
  ⟨PrimeFieldSizing.modulus_prime _ _⟩

theorem dwz63SharpHashModulus_char_floor (degree : ℕ) : 15625 ≤ dwz63SharpHashModulus degree :=
  le_of_lt (PrimeFieldSizing.characteristicFloor_lt_modulus _ _)

theorem dwz63SharpHashModulus_requirement (degree : ℕ) :
    8 * degree ≤ dwz63SharpHashModulus degree :=
  le_of_lt (PrimeFieldSizing.requirement_lt_modulus _ _)

theorem dwz63SharpHashModulus_le (degree : ℕ) :
    dwz63SharpHashModulus degree ≤ 2 * (15625 + 8 * degree + 1) :=
  PrimeFieldSizing.modulus_le_two_mul_add _ _

instance dwz63SharpHashModulus_neZero (degree : ℕ) : NeZero (dwz63SharpHashModulus degree) :=
  ⟨(dwz63SharpHashModulus_fact_prime degree).out.ne_zero⟩

/-- The hashing field at a client-supplied degree. -/
abbrev dwz63SharpHashField (degree : ℕ) : Type := ZMod (dwz63SharpHashModulus degree)

instance dwz63SharpHashField_neZero_two (degree : ℕ) :
    NeZero (2 : dwz63SharpHashField degree) :=
  neZero_two_zmod_of_three_le (by have := dwz63SharpHashModulus_char_floor degree; omega)

@[simp] theorem card_dwz63SharpHashField (degree : ℕ) :
    Fintype.card (dwz63SharpHashField degree) = dwz63SharpHashModulus degree :=
  ZMod.card _

/-- The retention loss at a client-supplied degree, factored as in
`Examples/DuanWuZhouLevelTwoHashRetention.lean`. -/
noncomputable def dwz63SharpModulusLoss (degree : ℕ) : ℝ :=
  4 * (2 * (15625 + 8 * (degree : ℝ) + 1))

/-- The subexponential Behrend factor at a client-supplied degree. -/
noncomputable def dwz63SharpBehrendLoss (degree : ℕ) : ℝ :=
  Real.exp (4 * Real.sqrt (Real.log ((dwz63SharpHashModulus degree / 2 : ℕ) : ℝ)))

/-- The retention loss at a client-supplied degree. -/
noncomputable def dwz63SharpRetentionLoss (degree : ℕ) : ℝ :=
  dwz63SharpModulusLoss degree * dwz63SharpBehrendLoss degree

theorem dwz63SharpModulusLoss_pos (degree : ℕ) : 0 < dwz63SharpModulusLoss degree := by
  unfold dwz63SharpModulusLoss
  have : (0 : ℝ) ≤ (degree : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem dwz63SharpBehrendLoss_pos (degree : ℕ) : 0 < dwz63SharpBehrendLoss degree :=
  Real.exp_pos _

/-- **Hash retention at any certified leg-fiber degree.**

Identical to `dwz63_retained_card_lower` except that the crude degree
`dwz63AmbientDegree n = 11390625 ^ (n+1)` is replaced by whatever `degree` the client can certify
for its own marked family, through the single hypothesis `hsharp`.  At
`degree = dwz63SharpDegree N_triple N_X` this is `[DuanWuZhou2022]`'s own bound, and the loss
`dwz63SharpModulusLoss degree` is then the rate-carrying `4M ≍ N_triple / N_X` rather than the
vacuous ambient count.

`hsharp` is the *only* undischarged input, and it is exactly the method-of-types statement
`MatrixMultiplication/CompatibilityIsolationCounting.lean`'s `ConditionalCompetitorEncoding`
supplies: the ambient targets sharing a leg word with a marked target are counted by a conditional
type class. -/
theorem dwz63_retained_card_lower_sharp (K : Type u) [CommRing K] (n degree : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (hsharp : ∀ c : Leg,
      ∀ triple ∈ (dwz63SymSixHashEncoding K (dwz63SharpHashField degree)
        (dwz63SharpHashModulus_char_floor degree)).legalTargets n markedWords,
        (ProgressionHash.LegalTriple.legFiber
          ((dwz63SymSixHashEncoding K (dwz63SharpHashField degree)
            (dwz63SharpHashModulus_char_floor degree)).legalTargets n Finset.univ)
          triple c).card ≤ degree) :
    ∃ (B : Finset (dwz63SharpHashField degree))
      (seed : ProgressionHash.Seed (dwz63SharpHashField degree) (Fin (n + 1))),
      ThreeAPFree (B : Set (dwz63SharpHashField degree)) ∧
        (markedWords.card : ℝ) ≤ dwz63SharpRetentionLoss degree *
          ((dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor degree) n
            markedWords B seed).card : ℝ) := by
  classical
  obtain ⟨B, hcardB, hfreeB⟩ := exists_threeAPFree_zmod_half (dwz63SharpHashModulus degree)
  have hmod : 8 * degree ≤ Fintype.card (dwz63SharpHashField degree) := by
    rw [card_dwz63SharpHashField]
    exact dwz63SharpHashModulus_requirement degree
  obtain ⟨seed, hcount⟩ :=
    exists_seed_dwz63JointRetained K (dwz63SharpHashModulus_char_floor degree) n
      markedWords B hfreeB degree (hsharp .X) (hsharp .Y) hmod
  refine ⟨B, seed, hfreeB, ?_⟩
  set retained := (dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor degree) n
    markedWords B seed).card with hretained
  rw [card_dwz63SharpHashField] at hcount
  have hreal : (3 * (markedWords.card : ℝ)) *
      (rothNumberNat (dwz63SharpHashModulus degree / 2) : ℝ) ≤
      (4 * (retained : ℝ)) *
        ((dwz63SharpHashModulus degree : ℝ) * (dwz63SharpHashModulus degree : ℝ)) := by
    have hnat : 3 * markedWords.card * B.card ≤
        4 * (dwz63SharpHashModulus degree * dwz63SharpHashModulus degree) * retained := hcount
    have hcast : ((3 * markedWords.card * B.card : ℕ) : ℝ) ≤
        ((4 * (dwz63SharpHashModulus degree * dwz63SharpHashModulus degree) * retained : ℕ) : ℝ) := by
      exact_mod_cast hnat
    rw [hcardB] at hcast
    push_cast at hcast
    linarith
  have hM : 2 ≤ dwz63SharpHashModulus degree := by
    have := dwz63SharpHashModulus_char_floor degree; omega
  have hMU : (dwz63SharpHashModulus degree : ℝ) ≤ 2 * (15625 + 8 * (degree : ℝ) + 1) := by
    have := dwz63SharpHashModulus_le degree
    have hcast : ((dwz63SharpHashModulus degree : ℕ) : ℝ) ≤
        ((2 * (15625 + 8 * degree + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast
    linarith
  have hkey := Growth.le_mul_exp_of_mul_rothNumberNat_le (M := dwz63SharpHashModulus degree)
    (a := 3 * (markedWords.card : ℝ)) (b := 4 * (retained : ℝ))
    (U := 2 * (15625 + 8 * (degree : ℝ) + 1))
    (t := 4 * Real.sqrt (Real.log ((dwz63SharpHashModulus degree / 2 : ℕ) : ℝ)))
    hM (by positivity) (by positivity) hMU le_rfl hreal
  have hexp : (0 : ℝ) < dwz63SharpBehrendLoss degree := dwz63SharpBehrendLoss_pos degree
  unfold dwz63SharpRetentionLoss dwz63SharpModulusLoss dwz63SharpBehrendLoss
  unfold dwz63SharpBehrendLoss at hexp
  nlinarith [hkey, hexp, Nat.cast_nonneg (α := ℝ) retained]

/-! ## The exponential-rate statement the count lane owes -/

/-- **Stated, not proved.**  The exponential form of `PREP.md` §4.3 (a)/(d): at word length `N`,
the `X`-marginal typical count divided by the sharp degree realizes `exp dwz63EntropyX` per index
position, up to a subexponential loss.  `loss` is the client's own polynomial/subexponential
factor; the six-fold exponent is the six orientations of the source power.

This is the identity that puts `exp H_X / K` into `dwz63TrueCopyRate`.  It is named here so the
count lane and this lane agree on its shape before either proves it; nothing in this module
depends on it. -/
def Dwz63SharpRateStatement (xCount : ℕ → ℕ) (jointCount : ℕ → ℕ) (loss : ℕ → ℝ) : Prop :=
  Growth.Subexponential loss ∧
    ∀ N : ℕ, 0 < N →
      Real.exp (dwz63EntropyX * (6 * N : ℕ)) ≤
        loss N * ((xCount N : ℝ) / (dwz63SharpDegree (jointCount N) (xCount N) : ℝ))

end AlgebraicComplexity.Examples
