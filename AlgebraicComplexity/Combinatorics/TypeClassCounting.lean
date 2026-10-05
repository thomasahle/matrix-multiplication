/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.CopyGrowth
import AlgebraicComplexity.Analysis.ProportionalTypeClassGrowth
import AlgebraicComplexity.Analysis.StructuralZeroMultinomialEntropy
import AlgebraicComplexity.Combinatorics.TypeClassEntropyLowerCore

set_option autoImplicit false

/-!
# The method of types at an arbitrary word length

`Combinatorics/WordType.lean` supplies the exact finite objects — `types`, `typeClass`,
`multiplicity`, and the multinomial identity — and `Analysis/ProportionalMultinomial.lean` /
`Analysis/StructuralZeroMultinomial.lean` supply the Stirling comparison, but only along the
*proportional* profiles `k ⋅ a`.  Several clients need the same estimates at an **arbitrary**
legal type `a ∈ types ι n`, where `n` is not presented as a multiple of a fixed profile mass.
This file is that layer.  It is generic in the finite alphabet and in the type: no tensor, no
certificate constant, no named matrix-multiplication object occurs.

The finite directed lower bound and its base-two conversion are defined in
`TypeClassEntropyLowerCore`.  This omnibus module adds subexponential growth, upper bounds,
conditional fibers, pigeonholes, and cutoff removal; clients that need only the lower bound should
import the core directly.

## The two losses

Every estimate here pays one of exactly two explicit, positive, subexponential factors, both
phrased in the `Growth.Subexponential` vocabulary the sequence layer consumes rather than as an
asymptotic `o(n)`:

* `typeCountLoss ι n = (n + 1) ^ |ι|` bounds the *number of types*, and is what a pigeonhole over
  types costs (`card_types_le_typeCountLoss`, `typeCountLoss_subexponential`);
* `typeClassEntropyLoss ι n = e ^ |ι| · (n + 1) ^ |ι|` is the *Stirling* loss separating one type
  class from its entropy exponent (`typeClassEntropyLoss_subexponential`).  It is the arbitrary-`n`
  envelope of `structuralZeroMultinomialLoss` (`Analysis/StructuralZeroMultinomial.lean`), taken at
  repetition one and coarsened by `a i ≤ n`.

## The statements

* **The pair.**  `card_typeClass_le_exp_profileEntropy` (upper, loss-free) and
  `exp_profileEntropy_le_typeClassEntropyLoss_mul_card_typeClass` (lower, explicit loss) are the
  two halves of `|T(a)| ≍ e^{n H(a)}`.
* **The pigeonhole.**  `exists_type_card_le_card_types_mul_card_filter` is division-free over `ℕ`:
  every finite family of length-`n` words has an empirical type retaining a `1/(n+1)^{|ι|}`
  fraction of it.  `exists_type_alphabet_pow_le_card_types_mul_card_typeClass` is its whole-cube
  specialization, i.e. the *ambient* method-of-types lower bound in its purest form.
* **The conditional pair.**
  `card_typedWordMapFiber_le_typeClassEntropyLoss_mul_exp_entropyDifference` and its converse
  `exp_entropyDifference_le_typeClassEntropyLoss_mul_card_typedWordMapFiber` bound one
  conditional fibre by `e^{n(H(a) − H(f_*a))}` in both directions.  They are corollaries of the
  *exact* committed quotient/fibre identity `card_targetType_mul_card_typedWordMapFiber`
  (`Combinatorics/WordType.lean`), so no new counting argument is introduced.
* **Base two.**  `profileEntropyBits` and `two_rpow_mul_profileEntropyBits` restate all of the
  above with a literal `2 ^ (n · H)` on one side, which is the shape sequence-level clients state
  their exponents in, and `exists_subexponential_loss_two_rpow_pow_le_mul_card_typeClass` packages
  the fixed-profile case as the existential `∃ loss, Subexponential loss ∧ base ^ k ≤ loss k · card`
  that a copy-count obligation consumes verbatim.
* **Loss-free after a cutoff.**  `exists_cutoff_forall_pow_le_card_proportionalTypeClass` runs that
  existential through the committed
  `Growth.Subexponential.exists_forall_pow_le_natCast_of_pow_le_mul`
  (`Analysis/CopyGrowth.lean`): every base strictly below the profile's rate is attained by the
  exact type-class cardinality itself, with **no** remaining loss factor.  A sequence-level client
  then absorbs the finite prefix with `Growth.finitePrefixPowerLoss`
  (`Analysis/EventualCopyGrowth.lean`) and never asks this layer for a loss sequence.

Nothing here supersedes the proportional-profile development: when a client already has its
profile presented as `k ⋅ a`, `proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass`
is sharper, since `∏ (a i · k + 1)` beats `(n + 1)^{|ι|}` whenever the profile is unbalanced.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u v

variable {ι : Type u} [Fintype ι]

/-! ### The two explicit losses -/

/-- The number-of-types loss.  This is the polynomial factor paid by any pigeonhole that replaces
a family of length-`n` words by one of its empirical type classes. -/
noncomputable def typeCountLoss (ι : Type u) [Fintype ι] (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)) ^ Fintype.card ι

theorem typeCountLoss_pos (ι : Type u) [Fintype ι] (n : ℕ) : 0 < typeCountLoss ι n := by
  unfold typeCountLoss
  positivity

/-- The number-of-types loss is polynomial, hence subexponential in the word length. -/
theorem typeCountLoss_subexponential (ι : Type u) [Fintype ι] :
    Growth.Subexponential (typeCountLoss ι) :=
  Growth.Subexponential.natCast_succ_pow (Fintype.card ι)

theorem card_types_le_typeCountLoss (ι : Type u) [Fintype ι] (n : ℕ) :
    ((types ι n).card : ℝ) ≤ typeCountLoss ι n := by
  unfold typeCountLoss
  exact_mod_cast card_types_le ι n

/-- The type-class entropy loss is polynomial, hence subexponential in the word length. -/
theorem typeClassEntropyLoss_subexponential (ι : Type u) [Fintype ι] :
    Growth.Subexponential (typeClassEntropyLoss ι) := by
  have hconst : (0 : ℝ) ≤ Real.exp 1 ^ Fintype.card ι := by positivity
  exact (Growth.Subexponential.natCast_succ_pow (Fintype.card ι)).const_mul hconst

/-! ### The method-of-types pair at an arbitrary word length -/

/-- Method-of-types upper bound, with **no** loss term: a type class never exceeds its entropy
exponent.  This is `multinomial_le_exp_profileEntropy` read through the multinomial identity. -/
theorem card_typeClass_le_exp_profileEntropy {n : ℕ} (a : ι → ℕ) (ha : a ∈ types ι n)
    (hn : 0 < n) :
    (((typeClass n a).card : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * profileEntropyNats a) := by
  have hmass : profileMass a = n := profileMass_eq_of_mem_types ha
  have hbound := multinomial_le_exp_profileEntropy a (by rw [hmass]; exact hn)
  rw [hmass] at hbound
  rw [card_typeClass_eq_multinomial a ha]
  exact hbound

/-- A word family confined to a single empirical type is bounded by that type's entropy exponent,
with no loss.  This is the shape a competitor-encoding hypothesis produces. -/
theorem card_le_exp_profileEntropy_of_forall_multiplicity_eq {n : ℕ}
    (words : Finset (Fin n → ι)) (a : ι → ℕ) (ha : a ∈ types ι n) (hn : 0 < n)
    (hwords : ∀ word ∈ words, multiplicity word = a) :
    ((words.card : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * profileEntropyNats a) := by
  have hsub : words ⊆ typeClass n a := fun word hword ↦ mem_typeClass.mpr (hwords word hword)
  calc ((words.card : ℕ) : ℝ) ≤ (((typeClass n a).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ Real.exp ((n : ℝ) * profileEntropyNats a) := card_typeClass_le_exp_profileEntropy a ha hn

/-- **The type pigeonhole against a uniform entropy ceiling.**

A finite family of length-`n` words whose *every occupied* empirical type has entropy at most `c`
has cardinality at most `(n + 1) ^ (card alphabet) * e ^ (n c)`.  The two inputs are this module's
type pigeonhole and its loss-free upper bound `card_typeClass_le_exp_profileEntropy`; nothing here
is specific to any matrix-multiplication construction. -/
theorem card_le_typeCountLoss_mul_exp_of_entropy_le {ι : Type*} [Fintype ι] {n : ℕ}
    (hn : 0 < n) (words : Finset (Fin n → ι)) (c : ℝ)
    (hwords : ∀ a ∈ WordType.types ι n,
      (words.filter fun w ↦ WordType.multiplicity w = a).Nonempty →
        WordType.profileEntropyNats a ≤ c) :
    (((words.card : ℕ)) : ℝ) ≤ WordType.typeCountLoss ι n * Real.exp ((n : ℝ) * c) := by
  classical
  have hfiber : words.card =
      ∑ a ∈ WordType.types ι n,
        (words.filter fun w ↦ WordType.multiplicity w = a).card :=
    Finset.card_eq_sum_card_fiberwise fun w _ ↦ WordType.multiplicity_mem_types w
  have hterm : ∀ a ∈ WordType.types ι n,
      (((words.filter fun w ↦ WordType.multiplicity w = a).card : ℕ) : ℝ)
        ≤ Real.exp ((n : ℝ) * c) := by
    intro a ha
    rcases Finset.eq_empty_or_nonempty (words.filter fun w ↦ WordType.multiplicity w = a) with
      hempty | hne
    · rw [hempty]
      simpa using (Real.exp_pos ((n : ℝ) * c)).le
    · have hsub : (words.filter fun w ↦ WordType.multiplicity w = a) ⊆
          WordType.typeClass n a := by
        intro w hw
        exact WordType.mem_typeClass.mpr (Finset.mem_filter.mp hw).2
      calc (((words.filter fun w ↦ WordType.multiplicity w = a).card : ℕ) : ℝ)
          ≤ (((WordType.typeClass n a).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ Real.exp ((n : ℝ) * WordType.profileEntropyNats a) :=
            WordType.card_typeClass_le_exp_profileEntropy a ha hn
        _ ≤ Real.exp ((n : ℝ) * c) :=
            Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left (hwords a ha hne) (Nat.cast_nonneg n))
  have hcast : (((words.card : ℕ)) : ℝ) =
      ∑ a ∈ WordType.types ι n,
        (((words.filter fun w ↦ WordType.multiplicity w = a).card : ℕ) : ℝ) := by
    rw [hfiber]
    push_cast
    ring
  calc (((words.card : ℕ)) : ℝ)
      = ∑ a ∈ WordType.types ι n,
          (((words.filter fun w ↦ WordType.multiplicity w = a).card : ℕ) : ℝ) := hcast
    _ ≤ ∑ _a ∈ WordType.types ι n, Real.exp ((n : ℝ) * c) := Finset.sum_le_sum hterm
    _ = (((WordType.types ι n).card : ℕ) : ℝ) * Real.exp ((n : ℝ) * c) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ WordType.typeCountLoss ι n * Real.exp ((n : ℝ) * c) :=
        mul_le_mul_of_nonneg_right (WordType.card_types_le_typeCountLoss ι n)
          (Real.exp_pos ((n : ℝ) * c)).le

/-! ### The type pigeonhole and the ambient lower bound -/

/-- Method-of-types pigeonhole for an **arbitrary** finite family of length-`n` words: some
empirical type retains a `1 / (n + 1)^{|ι|}` fraction of the family.  The statement is over `ℕ`
and therefore division-free and rounding-free. -/
theorem exists_type_card_le_card_types_mul_card_filter {n : ℕ}
    (words : Finset (Fin n → ι)) (hwords : words.Nonempty) :
    ∃ a ∈ types ι n,
      words.card ≤ (n + 1) ^ Fintype.card ι *
        (words.filter fun word ↦ multiplicity word = a).card := by
  classical
  have hsum : words.card =
      ∑ b ∈ types ι n, (words.filter fun word ↦ multiplicity word = b).card :=
    Finset.card_eq_sum_card_fiberwise fun word _ ↦ multiplicity_mem_types word
  obtain ⟨witness, hwitness⟩ := hwords
  have hne : (types ι n).Nonempty := ⟨multiplicity witness, multiplicity_mem_types witness⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (types ι n)
    (fun b ↦ (words.filter fun word ↦ multiplicity word = b).card) hne
  refine ⟨a, ha, ?_⟩
  calc words.card = ∑ b ∈ types ι n, (words.filter fun word ↦ multiplicity word = b).card := hsum
    _ ≤ (types ι n).card * (words.filter fun word ↦ multiplicity word = a).card := by
        simpa using Finset.sum_le_card_nsmul (types ι n)
          (fun b ↦ (words.filter fun word ↦ multiplicity word = b).card) _ hmax
    _ ≤ (n + 1) ^ Fintype.card ι *
        (words.filter fun word ↦ multiplicity word = a).card :=
        Nat.mul_le_mul_right _ (card_types_le ι n)

/-- Real-valued restatement of the type pigeonhole against the named subexponential loss. -/
theorem exists_type_card_le_typeCountLoss_mul_card_filter {n : ℕ}
    (words : Finset (Fin n → ι)) (hwords : words.Nonempty) :
    ∃ a ∈ types ι n,
      ((words.card : ℕ) : ℝ) ≤ typeCountLoss ι n *
        (((words.filter fun word ↦ multiplicity word = a).card : ℕ) : ℝ) := by
  classical
  obtain ⟨a, ha, hbound⟩ := exists_type_card_le_card_types_mul_card_filter words hwords
  refine ⟨a, ha, ?_⟩
  unfold typeCountLoss
  exact_mod_cast hbound

/-- The ambient method-of-types lower bound in its purest form: the whole cube of length-`n` words
is captured, up to the polynomial number of types, by a single empirical type class. -/
theorem exists_type_alphabet_pow_le_card_types_mul_card_typeClass [Nonempty ι] (n : ℕ) :
    ∃ a ∈ types ι n,
      Fintype.card ι ^ n ≤ (n + 1) ^ Fintype.card ι * (typeClass n a).card := by
  classical
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (types ι n)
    (fun b ↦ (typeClass n b).card) (types_nonempty ι n)
  refine ⟨a, ha, ?_⟩
  calc Fintype.card ι ^ n = ∑ b ∈ types ι n, (typeClass n b).card := (sum_card_classes ι n).symm
    _ ≤ (types ι n).card * (typeClass n a).card := by
        simpa using Finset.sum_le_card_nsmul (types ι n)
          (fun b ↦ (typeClass n b).card) _ hmax
    _ ≤ (n + 1) ^ Fintype.card ι * (typeClass n a).card :=
        Nat.mul_le_mul_right _ (card_types_le ι n)

/-- Real-valued restatement of the ambient lower bound against the named subexponential loss. -/
theorem exists_type_alphabet_pow_le_typeCountLoss_mul_card_typeClass [Nonempty ι] (n : ℕ) :
    ∃ a ∈ types ι n,
      ((Fintype.card ι : ℝ)) ^ n ≤ typeCountLoss ι n * (((typeClass n a).card : ℕ) : ℝ) := by
  obtain ⟨a, ha, hbound⟩ := exists_type_alphabet_pow_le_card_types_mul_card_typeClass (ι := ι) n
  refine ⟨a, ha, ?_⟩
  unfold typeCountLoss
  exact_mod_cast hbound

/-- The number of **joint** types over a product alphabet is polynomial in the word length with
the product exponent.  This is the estimate a joint-type pigeonhole pays. -/
theorem card_types_prod_le (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ] (n : ℕ) :
    (types (ι × κ) n).card ≤ (n + 1) ^ (Fintype.card ι * Fintype.card κ) := by
  simpa [Fintype.card_prod] using card_types_le (ι × κ) n

/-! ### The conditional pair -/

/-- Conditional method-of-types **upper** bound: one fibre of the exact quotient/fibre
factorization is at most the entropy difference, up to the target alphabet's polynomial loss.
The exact identity is `card_targetType_mul_card_typedWordMapFiber`; only the two entropy
comparisons above are added. -/
theorem card_typedWordMapFiber_le_typeClassEntropyLoss_mul_exp_entropyDifference
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] {n : ℕ}
    (f : α → β) (a : α → ℕ) (ha : a ∈ types α n) (hn : 0 < n)
    (target : Fin n → β) (htarget : target ∈ typeClass n (mappedType f a)) :
    (((typedWordMapFiber f a target).card : ℕ) : ℝ) ≤
      typeClassEntropyLoss β n *
        Real.exp ((n : ℝ) *
          (profileEntropyNats a - profileEntropyNats (mappedType f a))) := by
  have hmapped : mappedType f a ∈ types β n := by
    have hmem := multiplicity_mem_types target
    rwa [mem_typeClass.mp htarget] at hmem
  have hid : (((typeClass n (mappedType f a)).card : ℕ) : ℝ) *
      (((typedWordMapFiber f a target).card : ℕ) : ℝ) =
      (((typeClass n a).card : ℕ) : ℝ) := by
    exact_mod_cast card_targetType_mul_card_typedWordMapFiber f a target htarget
  have hexp : Real.exp ((n : ℝ) * profileEntropyNats (mappedType f a)) *
      Real.exp ((n : ℝ) *
        (profileEntropyNats a - profileEntropyNats (mappedType f a))) =
      Real.exp ((n : ℝ) * profileEntropyNats a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine le_of_mul_le_mul_left ?_ (Real.exp_pos ((n : ℝ) * profileEntropyNats (mappedType f a)))
  calc Real.exp ((n : ℝ) * profileEntropyNats (mappedType f a)) *
        (((typedWordMapFiber f a target).card : ℕ) : ℝ)
      ≤ (typeClassEntropyLoss β n * (((typeClass n (mappedType f a)).card : ℕ) : ℝ)) *
          (((typedWordMapFiber f a target).card : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right
          (exp_profileEntropy_le_typeClassEntropyLoss_mul_card_typeClass _ hmapped hn)
          (by positivity)
    _ = typeClassEntropyLoss β n * ((((typeClass n (mappedType f a)).card : ℕ) : ℝ) *
          (((typedWordMapFiber f a target).card : ℕ) : ℝ)) := by ring
    _ = typeClassEntropyLoss β n * (((typeClass n a).card : ℕ) : ℝ) := by rw [hid]
    _ ≤ typeClassEntropyLoss β n * Real.exp ((n : ℝ) * profileEntropyNats a) :=
        mul_le_mul_of_nonneg_left (card_typeClass_le_exp_profileEntropy a ha hn)
          (typeClassEntropyLoss_pos β n).le
    _ = Real.exp ((n : ℝ) * profileEntropyNats (mappedType f a)) *
        (typeClassEntropyLoss β n *
          Real.exp ((n : ℝ) *
            (profileEntropyNats a - profileEntropyNats (mappedType f a)))) := by
        rw [← hexp]; ring

/-- Conditional method-of-types **lower** bound: one fibre of the exact quotient/fibre
factorization attains the entropy difference, up to the source alphabet's polynomial loss. -/
theorem exp_entropyDifference_le_typeClassEntropyLoss_mul_card_typedWordMapFiber
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] {n : ℕ}
    (f : α → β) (a : α → ℕ) (ha : a ∈ types α n) (hn : 0 < n)
    (target : Fin n → β) (htarget : target ∈ typeClass n (mappedType f a)) :
    Real.exp ((n : ℝ) *
        (profileEntropyNats a - profileEntropyNats (mappedType f a))) ≤
      typeClassEntropyLoss α n *
        (((typedWordMapFiber f a target).card : ℕ) : ℝ) := by
  have hmapped : mappedType f a ∈ types β n := by
    have hmem := multiplicity_mem_types target
    rwa [mem_typeClass.mp htarget] at hmem
  have hid : (((typeClass n (mappedType f a)).card : ℕ) : ℝ) *
      (((typedWordMapFiber f a target).card : ℕ) : ℝ) =
      (((typeClass n a).card : ℕ) : ℝ) := by
    exact_mod_cast card_targetType_mul_card_typedWordMapFiber f a target htarget
  have hexp : Real.exp ((n : ℝ) * profileEntropyNats (mappedType f a)) *
      Real.exp ((n : ℝ) *
        (profileEntropyNats a - profileEntropyNats (mappedType f a))) =
      Real.exp ((n : ℝ) * profileEntropyNats a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine le_of_mul_le_mul_left ?_ (Real.exp_pos ((n : ℝ) * profileEntropyNats (mappedType f a)))
  calc Real.exp ((n : ℝ) * profileEntropyNats (mappedType f a)) *
        Real.exp ((n : ℝ) *
          (profileEntropyNats a - profileEntropyNats (mappedType f a)))
      = Real.exp ((n : ℝ) * profileEntropyNats a) := hexp
    _ ≤ typeClassEntropyLoss α n * (((typeClass n a).card : ℕ) : ℝ) :=
        exp_profileEntropy_le_typeClassEntropyLoss_mul_card_typeClass a ha hn
    _ = typeClassEntropyLoss α n * ((((typeClass n (mappedType f a)).card : ℕ) : ℝ) *
          (((typedWordMapFiber f a target).card : ℕ) : ℝ)) := by rw [hid]
    _ ≤ typeClassEntropyLoss α n * (Real.exp ((n : ℝ) * profileEntropyNats (mappedType f a)) *
          (((typedWordMapFiber f a target).card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (card_typeClass_le_exp_profileEntropy _ hmapped hn) (by positivity))
          (typeClassEntropyLoss_pos α n).le
    _ = Real.exp ((n : ℝ) * profileEntropyNats (mappedType f a)) *
        (typeClassEntropyLoss α n *
          (((typedWordMapFiber f a target).card : ℕ) : ℝ)) := by ring

/-! ### Base two -/

/-- Base-two form of the loss-free method-of-types upper bound. -/
theorem card_typeClass_le_two_rpow_profileEntropyBits {n : ℕ} (a : ι → ℕ)
    (ha : a ∈ types ι n) (hn : 0 < n) :
    (((typeClass n a).card : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * profileEntropyBits a) := by
  rw [two_rpow_mul_profileEntropyBits]
  exact card_typeClass_le_exp_profileEntropy a ha hn

/-- The exponential base of a fixed integral profile, in base two: repeating the profile `k`
times multiplies the entropy exponent by `k`. -/
theorem proportionalEntropyBase_eq_two_rpow (a : ι → ℕ) (hmass : 0 < profileMass a) :
    proportionalEntropyBase a =
      (2 : ℝ) ^ ((profileMass a : ℝ) * profileEntropyBits a) := by
  rw [two_rpow_mul_profileEntropyBits]
  exact proportionalEntropyBase_eq_exp_profileEntropy a hmass

/-- Sequence-ready ambient lower bound at a fixed integral profile, in base two: the exact `k`-fold
proportional type class attains the profile's base-two entropy rate up to the explicit
subexponential loss `structuralZeroMultinomialLoss`. -/
theorem two_rpow_profileEntropyBits_pow_le_structuralZeroLoss_mul_card_typeClass
    (a : ι → ℕ) (hmass : 0 < profileMass a) (k : ℕ) :
    ((2 : ℝ) ^ ((profileMass a : ℝ) * profileEntropyBits a)) ^ k ≤
      structuralZeroMultinomialLoss a k *
        (((typeClass (profileMass a * k) (proportionalCounts a k)).card : ℕ) : ℝ) := by
  rw [← proportionalEntropyBase_eq_two_rpow a hmass]
  exact proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass a k

/-- The packaged copy-count obligation: for every fixed integral profile there is a **named**
positive subexponential loss sequence against which the proportional type classes realize the
profile's base-two entropy rate.  This is the generic, certificate-free form of an ambient
`base ^ k ≤ loss k * card` requirement. -/
theorem exists_subexponential_loss_two_rpow_pow_le_mul_card_typeClass
    (a : ι → ℕ) (hmass : 0 < profileMass a) :
    ∃ loss : ℕ → ℝ, Growth.Subexponential loss ∧ (∀ k, 0 < loss k) ∧
      ∀ k, ((2 : ℝ) ^ ((profileMass a : ℝ) * profileEntropyBits a)) ^ k ≤
        loss k *
          (((typeClass (profileMass a * k) (proportionalCounts a k)).card : ℕ) : ℝ) :=
  ⟨structuralZeroMultinomialLoss a, structuralZeroMultinomialLoss_subexponential a,
    structuralZeroMultinomialLoss_pos a,
    two_rpow_profileEntropyBits_pow_le_structuralZeroLoss_mul_card_typeClass a hmass⟩

/-- The loss-free form of the ambient lower bound.  Every base strictly below the profile's
base-two entropy rate is attained, from some cutoff on, by the **exact integral cardinality** of
the proportional type class, with no remaining loss factor.  Positivity of that cardinality at
every repetition is `card_proportionalTypeClass_pos`, so a sequence-level client has both halves
of a copy-count obligation and can absorb the finite prefix with
`Growth.finitePrefixPowerLoss`. -/
theorem exists_cutoff_forall_pow_le_card_proportionalTypeClass
    (a : ι → ℕ) (hmass : 0 < profileMass a) {lowerBase : ℝ} (hlower : 0 < lowerBase)
    (hlt : lowerBase < (2 : ℝ) ^ ((profileMass a : ℝ) * profileEntropyBits a)) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k →
      lowerBase ^ k ≤
        (((typeClass (profileMass a * k) (proportionalCounts a k)).card : ℕ) : ℝ) := by
  obtain ⟨cutoff, hcutoff⟩ :=
    Growth.Subexponential.exists_forall_pow_le_natCast_of_pow_le_mul
      (structuralZeroMultinomialLoss_subexponential a) hlower hlt
  refine ⟨cutoff, fun k hk ↦ hcutoff k _ hk ?_⟩
  exact two_rpow_profileEntropyBits_pow_le_structuralZeroLoss_mul_card_typeClass a hmass k

end AlgebraicComplexity.WordType
