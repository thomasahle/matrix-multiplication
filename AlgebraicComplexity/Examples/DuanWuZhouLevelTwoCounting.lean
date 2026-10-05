/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalStage
import AlgebraicComplexity.Combinatorics.PrimeFieldSizing

/-!
# The level-two counting stage: the 15-cell distribution, its marginals, and the ambient estimates

`Examples/DuanWuZhouLevelTwoGlobalStage.lean` reduced `[DuanWuZhou2022]`'s `omega < 2.374631` to
the single hypothesis `DwzLevelTwoCountingStage`, and instantiated two of the six method-of-types
estimates that hypothesis unfolds into --- `N_X` and `N_Z`, at the *five-letter marginal* profiles
`dwz63AlphaX` and `dwz63AlphaZ`.  Those two profiles were introduced there as bare five-entry
tables, with no recorded relationship to the section 6.3 distribution they are marginals of.  This
module supplies the missing object and the two remaining ambient estimates.

## The 15-cell distribution

`dwz63Alpha` is the integral form of `global_value.tex`'s `table:result-2nd`: the fifteen level-two
components `(i, j, k)` with `i + j + k = 4`, in lexicographic order, weighted by `10 ^ 8` times the
paper's `alpha(i,j,k)`.  `dwz63XIndex`, `dwz63YIndex` and `dwz63ZIndex` read the three coordinates
off a component, and `dwz63Boundary` is the degeneracy test `i = 0 or j = 0`.

The three bridges

* `mappedType_dwz63XIndex_dwz63Alpha : mappedType dwz63XIndex dwz63Alpha = dwz63AlphaX`,
* `mappedType_dwz63YIndex_dwz63Alpha : mappedType dwz63YIndex dwz63Alpha = dwz63AlphaX`,
* `mappedType_dwz63ZIndex_dwz63Alpha : mappedType dwz63ZIndex dwz63Alpha = dwz63AlphaZ`

are what makes the previous module's estimates (b) and (c) estimates *about section 6.3's own
distribution* rather than about two unrelated five-letter profiles.  They are exact integer
identities and they are the reason `dwz63AlphaX` may be used for both `X` and `Y`: the level-two
distribution is symmetric in its first two coordinates.

## The ambient estimate (a)

`dwz63_ambientRate_pow_le_loss_mul_card_typeClass` is estimate (a) of
`better_bound/dwz_endpoint_prep/PREP.md` section 4.3.  It needs **no numerical value of
`H(alpha)`**: `2 ^ H(alpha)` cancels against `N_triple` in the copy rate, exactly as `ambientRate`
cancels in `GlobalRateData.copyRate_eq_min`.  So the estimate is stated with
`profileEntropyBits dwz63Alpha` left symbolic, and it is a direct instantiation of the generic
`Combinatorics/TypeClassCounting.lean` machinery at the 15-cell profile.

## The triple estimate (d), as one named hypothesis

Estimate (d) is `N_triple <= (n+1)^15 * max_{alpha' in D_alpha} 2 ^ (n H(alpha'))`, followed by
the *maximum-entropy* step that replaces the maximum by `2 ^ (n H(alpha)) * K ^ n`.  The first half
is proved here, unconditionally, as `dwz63_card_tripleSet_le_typeCountLoss_mul`; the second half is
isolated as the single named hypothesis `Dwz63TripleEntropyBound`, phrased entirely in
`Combinatorics/TypeClassCounting.lean`'s vocabulary (`types`, `mappedType`, `proportionalCounts`,
`profileEntropyNats`) and in the committed constant `dwz63HashLossMultiplier`.  It is the finite,
integral-profile shadow of `Probability/MaximumEntropyDual.maximumEntropyBits_le_coordinateDual`:
every legal type sharing the three coordinate marginals of `alpha` normalizes to a probability
vector with the same three marginals, and the committed `dwz63GibbsDeficit` certificate is exactly
the dual bound for those marginals.  `dwz63_tripleEntropyBound_premises` shows the reference
profile itself satisfies the three premises, so the hypothesis is not vacuous.

## Bertrand

Step (1) of PREP section 4.3 --- a prime modulus in `[M_0, 2 M_0]` --- is **not new work**:
`Combinatorics/PrimeFieldSizing.lean` already wraps `Nat.exists_prime_lt_and_le_two_mul`.
`dwz63_four_mul_modulus_le` is the one-line count-side client, the arithmetic form of the factor
`2` that step (4) of the chain pays.

## Position in the library

Layer 4 (a client).  It defines no tensor and proves no new generic counting theorem; every
estimate is an instantiation of `Combinatorics/TypeClassCounting.lean` or of
`Combinatorics/PrimeFieldSizing.lean` at the section 6.3 data.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3 and `table:result-2nd`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity

noncomputable section

/-! ## A generic compatibility of pushforward with proportional repetition -/

/-- Pushing a profile forward commutes with repeating it: `f_*(k a) = k (f_* a)`.  Both sides are
the same finite sum with the factor `k` pulled out. -/
theorem mappedType_proportionalCounts {A B : Type*} [Fintype A] (f : A → B) (a : A → ℕ)
    (k : ℕ) :
    WordType.mappedType f (WordType.proportionalCounts a k) =
      WordType.proportionalCounts (WordType.mappedType f a) k := by
  funext b
  show ∑ x ∈ WordType.letterFiber f b, a x * k = (∑ x ∈ WordType.letterFiber f b, a x) * k
  rw [Finset.sum_mul]

/-! ## The 15-cell distribution of section 6.3 -/

/-- **The level-two distribution of `[DuanWuZhou2022]` section 6.3**, `table:result-2nd`, as an
integral profile of total mass `10 ^ 8`.  The fifteen components `(i, j, k)` with `i + j + k = 4`
are listed in lexicographic order:

`(0,0,4) (0,1,3) (0,2,2) (0,3,1) (0,4,0) (1,0,3) (1,1,2) (1,2,1) (1,3,0) (2,0,2) (2,1,1) (2,2,0)
(3,0,1) (3,1,0) (4,0,0)`. -/
def dwz63Alpha : Fin 15 → ℕ :=
  ![20860, 1211153, 10366945, 1333318, 24731,
    1211153, 20088623, 20734458, 1251758,
    10366945, 20734458, 10045791,
    1333318, 1251758, 24731]

/-- The `X` coordinate `i` of each of the fifteen components. -/
def dwz63XIndex : Fin 15 → Fin 5 :=
  ![0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4]

/-- The `Y` coordinate `j` of each of the fifteen components. -/
def dwz63YIndex : Fin 15 → Fin 5 :=
  ![0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0]

/-- The `Z` coordinate `k` of each of the fifteen components. -/
def dwz63ZIndex : Fin 15 → Fin 5 :=
  ![4, 3, 2, 1, 0, 3, 2, 1, 0, 2, 1, 0, 1, 0, 0]

/-- `[DuanWuZhou2022]`'s degeneracy test `i = 0 or j = 0`: nine of the fifteen components are
boundary components, six are interior. -/
def dwz63Boundary : Fin 15 → Bool :=
  ![true, true, true, true, true,
    true, false, false, false,
    true, false, false,
    true, false, true]

theorem profileMass_dwz63Alpha : WordType.profileMass dwz63Alpha = 100000000 := by
  simp [WordType.profileMass, dwz63Alpha, Fin.sum_univ_succ]

theorem profileMass_dwz63Alpha_pos : 0 < WordType.profileMass dwz63Alpha := by
  rw [profileMass_dwz63Alpha]; norm_num

/-! ## The three marginals -/

/-- **The `X` marginal of the 15-cell distribution is `dwz63AlphaX`.**  This is the identity that
turns `Examples/DuanWuZhouLevelTwoGlobalStage.lean`'s estimate (b) into a statement about section
6.3's own distribution. -/
theorem mappedType_dwz63XIndex_dwz63Alpha :
    WordType.mappedType dwz63XIndex dwz63Alpha = dwz63AlphaX := by
  funext x
  rw [WordType.mappedType_eq_sum_ite]
  fin_cases x <;>
    simp [dwz63Alpha, dwz63XIndex, dwz63AlphaX, Fin.sum_univ_succ]

/-- **The `Y` marginal of the 15-cell distribution is also `dwz63AlphaX`.**  The level-two
distribution is symmetric under exchanging its first two coordinates, which is why one five-letter
table serves both legs. -/
theorem mappedType_dwz63YIndex_dwz63Alpha :
    WordType.mappedType dwz63YIndex dwz63Alpha = dwz63AlphaX := by
  funext y
  rw [WordType.mappedType_eq_sum_ite]
  fin_cases y <;>
    simp [dwz63Alpha, dwz63YIndex, dwz63AlphaX, Fin.sum_univ_succ]

/-- **The `Z` marginal of the 15-cell distribution is `dwz63AlphaZ`.**  This is the identity that
turns `Examples/DuanWuZhouLevelTwoGlobalStage.lean`'s estimate (c) into a statement about section
6.3's own distribution. -/
theorem mappedType_dwz63ZIndex_dwz63Alpha :
    WordType.mappedType dwz63ZIndex dwz63Alpha = dwz63AlphaZ := by
  funext z
  rw [WordType.mappedType_eq_sum_ite]
  fin_cases z <;>
    simp [dwz63Alpha, dwz63ZIndex, dwz63AlphaZ, Fin.sum_univ_succ]

/-- The `X` marginal of the repeated 15-cell profile is the repeated `X` marginal. -/
theorem mappedType_dwz63XIndex_proportionalCounts (k : ℕ) :
    WordType.mappedType dwz63XIndex (WordType.proportionalCounts dwz63Alpha k) =
      WordType.proportionalCounts dwz63AlphaX k := by
  rw [mappedType_proportionalCounts, mappedType_dwz63XIndex_dwz63Alpha]

/-- The `Y` marginal of the repeated 15-cell profile is the repeated `X` marginal. -/
theorem mappedType_dwz63YIndex_proportionalCounts (k : ℕ) :
    WordType.mappedType dwz63YIndex (WordType.proportionalCounts dwz63Alpha k) =
      WordType.proportionalCounts dwz63AlphaX k := by
  rw [mappedType_proportionalCounts, mappedType_dwz63YIndex_dwz63Alpha]

/-- The `Z` marginal of the repeated 15-cell profile is the repeated `Z` marginal. -/
theorem mappedType_dwz63ZIndex_proportionalCounts (k : ℕ) :
    WordType.mappedType dwz63ZIndex (WordType.proportionalCounts dwz63Alpha k) =
      WordType.proportionalCounts dwz63AlphaZ k := by
  rw [mappedType_proportionalCounts, mappedType_dwz63ZIndex_dwz63Alpha]

/-- The repeated 15-cell profile is a legal type of the corresponding word length. -/
theorem proportionalCounts_dwz63Alpha_mem_types (k : ℕ) :
    WordType.proportionalCounts dwz63Alpha k ∈
      WordType.types (Fin 15) (WordType.profileMass dwz63Alpha * k) := by
  rw [WordType.mem_types]
  show ∑ c, dwz63Alpha c * k = WordType.profileMass dwz63Alpha * k
  rw [← Finset.sum_mul]
  rfl

/-! ## Estimate (a): the ambient count `N_alpha` -/

/-- **Method-of-types estimate (a) of `PREP.md` section 4.3.**

The exact number of length-`10 ^ 8 k` words with the 15-cell profile realizes the profile's
base-two entropy rate, up to the named subexponential Stirling loss.  No numerical value of
`H(alpha)` is used or needed: in the copy rate `2 ^ H(alpha)` cancels against `N_triple`.

This is a direct instantiation of the generic
`WordType.two_rpow_profileEntropyBits_pow_le_structuralZeroLoss_mul_card_typeClass`; the only
DWZ-specific input is that the 15-cell profile has positive mass. -/
theorem dwz63_ambientRate_pow_le_loss_mul_card_typeClass (k : ℕ) :
    ((2 : ℝ) ^ ((WordType.profileMass dwz63Alpha : ℝ) *
        WordType.profileEntropyBits dwz63Alpha)) ^ k ≤
      WordType.structuralZeroMultinomialLoss dwz63Alpha k *
        (((WordType.typeClass (WordType.profileMass dwz63Alpha * k)
            (WordType.proportionalCounts dwz63Alpha k)).card : ℕ) : ℝ) :=
  WordType.two_rpow_profileEntropyBits_pow_le_structuralZeroLoss_mul_card_typeClass
    dwz63Alpha profileMass_dwz63Alpha_pos k

/-- The loss-free form of estimate (a): every base strictly below the 15-cell profile's rate is
attained, from some word length on, by the exact type-class cardinality itself. -/
theorem dwz63_exists_cutoff_pow_le_card_ambientTypeClass {lowerBase : ℝ} (hlower : 0 < lowerBase)
    (hlt : lowerBase < (2 : ℝ) ^ ((WordType.profileMass dwz63Alpha : ℝ) *
      WordType.profileEntropyBits dwz63Alpha)) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k →
      lowerBase ^ k ≤
        (((WordType.typeClass (WordType.profileMass dwz63Alpha * k)
            (WordType.proportionalCounts dwz63Alpha k)).card : ℕ) : ℝ) :=
  WordType.exists_cutoff_forall_pow_le_card_proportionalTypeClass dwz63Alpha
    profileMass_dwz63Alpha_pos hlower hlt

/-! ## Estimate (d): the triple count `N_triple` -/

/-- **`[DuanWuZhou2022]`'s `N_triple`**: the length-`n` words over the fifteen-component alphabet
whose three coordinate marginals are the prescribed ones.  A word here is one large triple
`(X_I, Y_J, Z_K)` read componentwise; the three marginal conditions are exactly the requirement
that its `X`-, `Y`- and `Z`-blocks have the prescribed types. -/
def dwz63TripleSet (n : ℕ) (aX aY aZ : Fin 5 → ℕ) : Finset (Fin n → Fin 15) := by
  classical
  exact Finset.univ.filter fun word ↦
    WordType.mappedType dwz63XIndex (WordType.multiplicity word) = aX ∧
      WordType.mappedType dwz63YIndex (WordType.multiplicity word) = aY ∧
      WordType.mappedType dwz63ZIndex (WordType.multiplicity word) = aZ

@[simp] theorem mem_dwz63TripleSet {n : ℕ} {aX aY aZ : Fin 5 → ℕ} {word : Fin n → Fin 15} :
    word ∈ dwz63TripleSet n aX aY aZ ↔
      WordType.mappedType dwz63XIndex (WordType.multiplicity word) = aX ∧
        WordType.mappedType dwz63YIndex (WordType.multiplicity word) = aY ∧
        WordType.mappedType dwz63ZIndex (WordType.multiplicity word) = aZ := by
  classical
  simp [dwz63TripleSet]

/-- **The one named hypothesis of `M-DWZ9`: the maximum-entropy step of estimate (d).**

Every legal type of the fifteen-component alphabet that shares the three coordinate marginals of
the repeated section 6.3 distribution has entropy at most `H(alpha) + log K`, where
`K = dwz63HashLossMultiplier = 1 + 10 ^ (-10)` is the committed hash-loss multiplier.  In
`[DuanWuZhou2022]`'s notation this is

`max_{alpha' in D_alpha} 2 ^ H(alpha') <= 2 ^ H(alpha) * K`,

the *only* genuinely new mathematics the count side of section 6.3 needs, and the statement whose
real-valued form is `Probability/MaximumEntropyDual.maximumEntropyBits_le_coordinateDual`
(`coordinateDualBits` instantiated at the three coordinate potentials of the committed
`dwz63GibbsDeficit`).  The vocabulary here --- `types`, `mappedType`, `proportionalCounts`,
`profileEntropyNats` --- is `Combinatorics/TypeClassCounting.lean`'s throughout, so a promotion of
that theorem to integral profiles drops straight in.

Everything else on the count side is stated and proved without it. -/
def Dwz63TripleEntropyBound : Prop :=
  ∀ (k : ℕ) (a : Fin 15 → ℕ),
    a ∈ WordType.types (Fin 15) (WordType.profileMass dwz63Alpha * k) →
    WordType.mappedType dwz63XIndex a = WordType.proportionalCounts dwz63AlphaX k →
    WordType.mappedType dwz63YIndex a = WordType.proportionalCounts dwz63AlphaX k →
    WordType.mappedType dwz63ZIndex a = WordType.proportionalCounts dwz63AlphaZ k →
    WordType.profileEntropyNats a ≤
      WordType.profileEntropyNats dwz63Alpha + Real.log dwz63HashLossMultiplier

/-- **Anti-vacuity for estimate (d)**: the reference profile is one of the competitors the named
hypothesis quantifies over, so its three premises are satisfiable and the hypothesis is a genuine
maximization over a nonempty family. -/
theorem dwz63_tripleEntropyBound_premises (k : ℕ) :
    WordType.proportionalCounts dwz63Alpha k ∈
        WordType.types (Fin 15) (WordType.profileMass dwz63Alpha * k) ∧
      WordType.mappedType dwz63XIndex (WordType.proportionalCounts dwz63Alpha k) =
        WordType.proportionalCounts dwz63AlphaX k ∧
      WordType.mappedType dwz63YIndex (WordType.proportionalCounts dwz63Alpha k) =
        WordType.proportionalCounts dwz63AlphaX k ∧
      WordType.mappedType dwz63ZIndex (WordType.proportionalCounts dwz63Alpha k) =
        WordType.proportionalCounts dwz63AlphaZ k :=
  ⟨proportionalCounts_dwz63Alpha_mem_types k,
    mappedType_dwz63XIndex_proportionalCounts k,
    mappedType_dwz63YIndex_proportionalCounts k,
    mappedType_dwz63ZIndex_proportionalCounts k⟩

/-- **Method-of-types estimate (d) of `PREP.md` section 4.3.**

`N_triple <= (n + 1) ^ 15 * e ^ (n (H(alpha) + log K))`: the triple count is at most the polynomial
number of types times the largest entropy exponent available to a competitor, and the named
hypothesis is exactly what bounds that largest exponent.  The pigeonhole and the loss-free upper
bound are supplied generically by `card_le_typeCountLoss_mul_exp_of_entropy_le`; all this proof
adds is that an occupied type of the triple family really does share the three marginals, which is
read off one witness word. -/
theorem dwz63_card_tripleSet_le_typeCountLoss_mul (h : Dwz63TripleEntropyBound) {k : ℕ}
    (hk : 0 < k) :
    (((dwz63TripleSet (WordType.profileMass dwz63Alpha * k)
        (WordType.proportionalCounts dwz63AlphaX k)
        (WordType.proportionalCounts dwz63AlphaX k)
        (WordType.proportionalCounts dwz63AlphaZ k)).card : ℕ) : ℝ) ≤
      WordType.typeCountLoss (Fin 15) (WordType.profileMass dwz63Alpha * k) *
        Real.exp (((WordType.profileMass dwz63Alpha * k : ℕ) : ℝ) *
          (WordType.profileEntropyNats dwz63Alpha + Real.log dwz63HashLossMultiplier)) := by
  classical
  have hnpos : 0 < WordType.profileMass dwz63Alpha * k := by
    rw [profileMass_dwz63Alpha]
    exact Nat.mul_pos (by norm_num) hk
  refine WordType.card_le_typeCountLoss_mul_exp_of_entropy_le hnpos _ _ ?_
  rintro a ha ⟨word, hword⟩
  rw [Finset.mem_filter] at hword
  obtain ⟨hmem, htype⟩ := hword
  rw [mem_dwz63TripleSet] at hmem
  obtain ⟨hX, hY, hZ⟩ := hmem
  rw [htype] at hX hY hZ
  exact h k a ha hX hY hZ

/-! ## Step (1) of the chain: Bertrand -/

/-- **Step (1) of `PREP.md` section 4.3's chain is already wrapped.**

`Combinatorics/PrimeFieldSizing.lean` supplies a prime `M` with `M_0 < M <= 2 M_0` from
`Nat.exists_prime_lt_and_le_two_mul`; the count-side consequence used in step (4) is that the
retained fraction `1 / (4 M)` is at least `1 / (8 (floor + M_0 + 1))`.  This is the whole of the
"factor two" the chain pays for choosing a prime modulus, and it is pure arithmetic. -/
theorem dwz63_four_mul_modulus_le (characteristicFloor requirement : ℕ) :
    4 * PrimeFieldSizing.modulus characteristicFloor requirement ≤
      8 * (characteristicFloor + requirement + 1) := by
  have h := PrimeFieldSizing.modulus_le_two_mul_add characteristicFloor requirement
  omega

/-- The Bertrand modulus of step (1) strictly exceeds the finite cardinality requirement it is
chosen for, which is the hypothesis every hashing client consumes. -/
theorem dwz63_requirement_lt_modulus (characteristicFloor requirement : ℕ) :
    requirement < PrimeFieldSizing.modulus characteristicFloor requirement :=
  PrimeFieldSizing.requirement_lt_modulus characteristicFloor requirement

end

end AlgebraicComplexity.Examples
