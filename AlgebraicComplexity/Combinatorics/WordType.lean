/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.MappedType
import AlgebraicComplexity.Combinatorics.WordTypeCardinalityCore
import AlgebraicComplexity.Combinatorics.WordTypeCore
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# Multiplicity types of finite words

Tensor powers of a finite direct sum are indexed by words.  The terms belonging to words with
the same letter multiplicities are isomorphic, and their number is only polynomial in the word
length.  This file develops that finite combinatorial layer independently of tensors.

The definitions deliberately use functions `Fin n → ι` for words and functions `ι → ℕ` for
types.  This agrees with Mathlib's `Finset.piAntidiag` and avoids choosing an ordering of the
finite alphabet.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u v

variable {ι : Type u} [Fintype ι]

/-- Words mapping coordinatewise to a prescribed target word. -/
noncomputable def wordMapFiber {α β : Type*} [Fintype α]
    (f : α → β) (target : Fin n → β) : Finset (Fin n → α) := by
  classical
  exact Finset.univ.filter fun word ↦ f ∘ word = target

/-- Words of one fixed source multiplicity type that map coordinatewise to a prescribed target
word.  This is the relevant competitor fiber in laser-method hashing: using `wordMapFiber`
instead would forget the selected joint type and can introduce an exponential overcount. -/
noncomputable def typedWordMapFiber {α β : Type*} [Fintype α]
    (f : α → β) (a : α → ℕ) (target : Fin n → β) : Finset (Fin n → α) := by
  classical
  exact (typeClass n a).filter fun word ↦ f ∘ word = target

@[simp] theorem mem_wordMapFiber {α β : Type*} [Fintype α]
    {f : α → β} {target : Fin n → β} {word : Fin n → α} :
    word ∈ wordMapFiber f target ↔ f ∘ word = target := by
  classical
  simp [wordMapFiber]

@[simp] theorem mem_typedWordMapFiber {α β : Type*} [Fintype α]
    {f : α → β} {a : α → ℕ} {target : Fin n → β} {word : Fin n → α} :
    word ∈ typedWordMapFiber f a target ↔
      multiplicity word = a ∧ f ∘ word = target := by
  classical
  simp [typedWordMapFiber, typeClass]

/-- A word fiber is the finite Cartesian product of its coordinate letter fibers. -/
theorem wordMapFiber_eq_piFinset {α β : Type*} [Fintype α]
    (f : α → β) (target : Fin n → β) :
    wordMapFiber f target = Fintype.piFinset (fun i ↦ letterFiber f (target i)) := by
  classical
  ext word
  simp only [mem_wordMapFiber, Fintype.mem_piFinset, mem_letterFiber]
  exact funext_iff

/-- Exact product formula for the number of coordinatewise lifts of a finite word. -/
theorem card_wordMapFiber {α β : Type*} [Fintype α]
    (f : α → β) (target : Fin n → β) :
    (wordMapFiber f target).card = ∏ i, (letterFiber f (target i)).card := by
  classical
  rw [wordMapFiber_eq_piFinset, Fintype.card_piFinset]

/-- The number of occurrences of a letter never exceeds the length of the word. -/
theorem multiplicity_le_length {n : ℕ} (word : Fin n → ι) (letter : ι) :
    multiplicity word letter ≤ n := by
  conv_rhs => rw [← sum_multiplicity word]
  exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ letter)

/-- A finite sum of a function that takes the constant value `c` away from one marked letter. -/
theorem sum_eq_of_const_off [Nonempty ι] [DecidableEq ι] (letter : ι) (f : ι → ℝ) (c : ℝ)
    (h : ∀ i, i ≠ letter → f i = c) :
    ∑ i, f i = f letter + ((Fintype.card ι : ℝ) - 1) * c := by
  classical
  have hcast : ((Finset.univ.erase letter).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ letter), Finset.card_univ]
    have h1 : 1 ≤ Fintype.card ι := Fintype.card_pos
    push_cast [Nat.cast_sub h1]
    ring
  calc
    ∑ i, f i = f letter + ∑ i ∈ Finset.univ.erase letter, f i :=
      (Finset.add_sum_erase _ f (Finset.mem_univ letter)).symm
    _ = f letter + ∑ _i ∈ Finset.univ.erase letter, c := by
      refine congrArg (f letter + ·) (Finset.sum_congr rfl fun i hi ↦ ?_)
      exact h i (Finset.ne_of_mem_erase hi)
    _ = f letter + ((Fintype.card ι : ℝ) - 1) * c := by
      rw [Finset.sum_const, nsmul_eq_mul, hcast]

omit [Fintype ι] in
/-- The letter occurring at any position has nonzero multiplicity in the word. -/
theorem multiplicity_apply_ne_zero (word : Fin n → ι) (position : Fin n) :
    multiplicity word (word position) ≠ 0 := by
  classical
  unfold multiplicity
  apply Finset.card_ne_zero.mpr
  exact ⟨position, by simp⟩

omit [Fintype ι] in
/-- Multiplicity in a constant finite word: its unique letter occurs at every position and all
other letters occur zero times. -/
theorem multiplicity_const [DecidableEq ι] (n : ℕ) (a b : ι) :
    multiplicity (fun _ : Fin n ↦ a) b = if b = a then n else 0 := by
  unfold multiplicity
  by_cases h : b = a
  · subst b
    simp
  · have hab : a ≠ b := fun h' ↦ h h'.symm
    simp [h, hab]

/-- The multiplicity of a letter after mapping an alphabet is the sum of the multiplicities in
its letter fiber. -/
theorem multiplicity_comp_eq_sum_letterFiber {α β : Type*} [Fintype α]
    (f : α → β) (word : Fin n → α) (b : β) :
    multiplicity (f ∘ word) b =
      ∑ a ∈ letterFiber f b, multiplicity word a := by
  classical
  unfold multiplicity
  simpa [Function.comp_apply] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin n)) (letterFiber f b) word).symm

/-- Coordinatewise mapping pushes the multiplicity type forward by summing over letter
fibers. -/
theorem multiplicity_comp_eq_mappedType {α β : Type*} [Fintype α]
    (f : α → β) (word : Fin n → α) :
    multiplicity (f ∘ word) = mappedType f (multiplicity word) := by
  funext b
  exact multiplicity_comp_eq_sum_letterFiber f word b

/-- The total mass of a pushed-forward multiplicity profile is the total mass of the profile. -/
theorem sum_mappedType {α : Type*} [Fintype α] {β : Type*} [Fintype β] [DecidableEq β]
    (f : α → β) (a : α → ℕ) : ∑ b, mappedType f a b = ∑ x, a x := by
  classical
  simp only [mappedType_eq_sum_ite]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ ↦ by simp

/-- Transporting the length of a word along an equality does not change its letter
multiplicities.  This equality-cast form is convenient when a regional decomposition stores its
total length as a proof rather than as a definitional sum. -/
theorem multiplicity_cast {α : Type*} [Fintype α] {n m : ℕ}
    (h : n = m) (word : Fin m → α) :
    multiplicity (word ∘ Fin.cast h) = multiplicity word := by
  subst m
  exact multiplicity_reindex (Equiv.refl (Fin n)) word

/-- Concatenating two words adds their letter multiplicities pointwise. -/
theorem multiplicity_append {α : Type*} [Fintype α]
    (left : Fin n → α) (right : Fin m → α) :
    multiplicity (Fin.append left right) = multiplicity left + multiplicity right := by
  classical
  funext a
  change multiplicity (Fin.append left right) a =
    multiplicity left a + multiplicity right a
  rw [multiplicity_eq_card_fiber, multiplicity_eq_card_fiber,
    multiplicity_eq_card_fiber]
  have happend :
      (fun i : Fin (n + m) ↦
        Sum.elim left right (finSumFinEquiv.symm i)) = Fin.append left right := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  let e₁ : {i // Fin.append left right i = a} ≃
      {s : Fin n ⊕ Fin m // Sum.elim left right s = a} :=
    finSumFinEquiv.symm.subtypeEquiv fun i ↦ by
      rw [congrFun happend i]
  let e : {i // Fin.append left right i = a} ≃
      {i // left i = a} ⊕ {i // right i = a} :=
    e₁.trans Equiv.subtypeSum
  simpa using Fintype.card_congr e

/-- Mapping a finite word through a permutation reindexes its multiplicity profile by the inverse
permutation. -/
theorem multiplicity_comp_perm_apply
    {n : ℕ} {U : Type u} [Fintype U] (perm : Equiv.Perm U)
    (word : Fin n → U) (u : U) :
    multiplicity (perm ∘ word) u = multiplicity word (perm.symm u) := by
  classical
  unfold multiplicity
  congr 1
  ext position
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · intro h
    calc
      word position = perm.symm (perm (word position)) := (perm.symm_apply_apply _).symm
      _ = perm.symm u := congrArg perm.symm h
  · intro h
    calc
      perm (word position) = perm (perm.symm u) := congrArg perm h
      _ = u := perm.apply_symm_apply u

/-- Appending a word to a permuted copy adds its profile to the inverse-permuted profile.  The two
occurrences remain labelled, so a fixed point contributes twice. -/
theorem multiplicity_append_complement_apply
    {n : ℕ} {U : Type u} [Fintype U] (perm : Equiv.Perm U)
    (left : Fin n → U) (u : U) :
    multiplicity (Fin.append left (perm ∘ left)) u =
      multiplicity left u + multiplicity left (perm.symm u) := by
  rw [multiplicity_append]
  change multiplicity left u + multiplicity (perm ∘ left) u = _
  rw [multiplicity_comp_perm_apply]

/-- Two words of the same multiplicity type differ only by a permutation of their positions.
The chosen permutation sends every fiber of `left` to the corresponding fiber of `right`. -/
noncomputable def positionPermOfSameMultiplicity {α : Type*} [Fintype α]
    (left right : Fin n → α) (h : multiplicity left = multiplicity right) :
    Equiv.Perm (Fin n) :=
  Equiv.ofFiberEquiv (f := left) (g := right) fun b ↦ by
    classical
    exact Fintype.equivOfCardEq <| by
      rw [← multiplicity_eq_card_fiber left b,
        ← multiplicity_eq_card_fiber right b, h]

theorem positionPermOfSameMultiplicity_map {α : Type*} [Fintype α]
    (left right : Fin n → α) (h : multiplicity left = multiplicity right) :
    right ∘ positionPermOfSameMultiplicity left right h = left := by
  funext i
  unfold positionPermOfSameMultiplicity
  exact Equiv.ofFiberEquiv_map _ i

/-- Typed coordinatewise fibers over target words of the same type have equal size.  The proof
reindexes positions by a permutation carrying one target word to the other. -/
theorem card_typedWordMapFiber_eq_of_multiplicity_eq
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (a : α → ℕ) (left right : Fin n → β)
    (h : multiplicity left = multiplicity right) :
    (typedWordMapFiber f a left).card =
      (typedWordMapFiber f a right).card := by
  classical
  let e := positionPermOfSameMultiplicity left right h
  have he : right ∘ e = left := positionPermOfSameMultiplicity_map left right h
  have he' : left ∘ e.symm = right := by
    funext i
    have hi := congrFun he (e.symm i)
    simpa [Function.comp_apply] using hi.symm
  apply Finset.card_bij (fun word _ ↦ word ∘ e.symm)
  · intro word hword
    rw [mem_typedWordMapFiber] at hword ⊢
    refine ⟨?_, ?_⟩
    · rw [multiplicity_reindex, hword.1]
    · exact (congrArg (fun g ↦ g ∘ e.symm) hword.2).trans he'
  · intro leftWord _hleft rightWord _hright heq
    funext i
    have hi := congrFun heq (e i)
    simpa [Function.comp_apply] using hi
  · intro word hword
    refine ⟨word ∘ e, ?_, ?_⟩
    · rw [mem_typedWordMapFiber] at hword ⊢
      refine ⟨?_, ?_⟩
      · have hm := multiplicity_reindex e.symm word
        simpa using hm.trans hword.1
      · exact (congrArg (fun g ↦ g ∘ e) hword.2).trans he
    · funext i
      simp [Function.comp_apply]

/-- Exact double counting for a fixed source type.  The source type class is partitioned by its
mapped target words, and every target word of the induced type has an equally large typed fiber.
This identity is the sharp finite competitor count needed by tight-support hashing. -/
theorem card_targetType_mul_card_typedWordMapFiber
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (a : α → ℕ) (target : Fin n → β)
    (htarget : target ∈ typeClass n (mappedType f a)) :
    (typeClass n (mappedType f a)).card *
        (typedWordMapFiber f a target).card =
      (typeClass n a).card := by
  classical
  symm
  calc
    (typeClass n a).card =
        ∑ b ∈ typeClass n (mappedType f a),
          ((typeClass n a).filter fun word ↦ f ∘ word = b).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun word hword ↦ by
        apply mem_typeClass.mpr
        rw [multiplicity_comp_eq_mappedType, mem_typeClass.mp hword])
    _ = ∑ _b ∈ typeClass n (mappedType f a),
          (typedWordMapFiber f a target).card := by
      apply Finset.sum_congr rfl
      intro b hb
      apply card_typedWordMapFiber_eq_of_multiplicity_eq
      exact (mem_typeClass.mp hb).trans (mem_typeClass.mp htarget).symm
    _ = (typeClass n (mappedType f a)).card *
          (typedWordMapFiber f a target).card := by simp

/-- Every coordinate of a type is at most the word length. -/
theorem coordinate_le {a : ι → ℕ} (ha : a ∈ types ι n) (i : ι) : a i ≤ n := by
  rw [mem_types] at ha
  rw [← ha]
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

/-- Encode a type by bounded coordinates.  This is the injection behind the polynomial bound on
the number of types. -/
def boundedEmbedding (n : ℕ) : {a // a ∈ types ι n} ↪ (ι → Fin (n + 1)) where
  toFun a i := ⟨a.1 i, Nat.lt_succ_iff.mpr (coordinate_le a.2 i)⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)

/-- The number of word types is at most `(n + 1)^|ι|`.  For a fixed alphabet this is polynomial
in `n`, which is the only estimate required in asymptotic type extraction. -/
theorem card_types_le (ι : Type u) [Fintype ι] (n : ℕ) :
    (types ι n).card ≤ (n + 1) ^ Fintype.card ι := by
  classical
  calc
    (types ι n).card = Fintype.card {a // a ∈ types ι n} := by simp
    _ ≤ Fintype.card (ι → Fin (n + 1)) :=
      Fintype.card_le_of_injective (boundedEmbedding (ι := ι) n)
        (boundedEmbedding (ι := ι) n).injective
    _ = (n + 1) ^ Fintype.card ι := by simp

/-- The type classes partition all words. -/
theorem sum_card_classes (ι : Type u) [Fintype ι] (n : ℕ) :
    ∑ a ∈ types ι n, (typeClass n a).card = Fintype.card ι ^ n := by
  classical
  simpa [typeClass] using (Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n → ι)))
    (t := types ι n)
    (f := multiplicity)
    (by intro word _; exact multiplicity_mem_types word)).symm

/-- Partition an arbitrary finite sum over words into multiplicity classes. -/
theorem sum_by_type {M : Type*} [AddCommMonoid M]
    (weight : (Fin n → ι) → M) :
    ∑ word, weight word =
      ∑ a ∈ types ι n, ∑ word ∈ typeClass n a, weight word := by
  classical
  exact (Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin n → ι)))
    (t := types ι n)
    (g := multiplicity)
    (by intro word _; exact multiplicity_mem_types word)
    weight).symm

/-- A product indexed by the positions of a word depends only on its multiplicity vector. -/
theorem prod_word_eq_prod_pow {M : Type*} [CommMonoid M]
    (x : ι → M) (word : Fin n → ι) :
    ∏ j, x (word j) = ∏ i, x i ^ multiplicity word i := by
  classical
  rw [← Finset.prod_fiberwise' (Finset.univ : Finset (Fin n)) word x]
  simp [multiplicity]

/-- Summing the product weight of every word gives the expected power. -/
theorem sum_prod_word_eq_pow {R : Type*} [CommSemiring R]
    (x : ι → R) (n : ℕ) :
    ∑ word : Fin n → ι, ∏ j, x (word j) = (∑ i, x i) ^ n := by
  classical
  exact (Fintype.sum_pow x n).symm

/-- Multinomial expansion grouped by actual word classes.  This form is particularly convenient
for tensor extraction: `#(class n a)` is literally the number of mutually disjoint word blocks
that survive after selecting type `a`. -/
theorem pow_sum_eq_sum_type_class {R : Type*} [CommSemiring R]
    (x : ι → R) (n : ℕ) :
    (∑ i, x i) ^ n =
      ∑ a ∈ types ι n, ((typeClass n a).card : R) * ∏ i, x i ^ a i := by
  classical
  rw [← sum_prod_word_eq_pow x n, sum_by_type]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ word ∈ typeClass n a, ∏ j, x (word j)) =
        ∑ _word ∈ typeClass n a, ∏ i, x i ^ a i := by
      apply Finset.sum_congr rfl
      intro word hword
      rw [prod_word_eq_prod_pow]
      exact congrArg (fun b : ι → ℕ ↦ ∏ i, x i ^ b i)
        (mem_typeClass.mp hword)
    _ = ((typeClass n a).card : R) * ∏ i, x i ^ a i := by simp

/-- The cardinality of a word class is the usual multinomial coefficient.  The identity is proved
in `AlgebraicComplexity.Combinatorics.WordTypeCardinalityCore`, inside the additive monoid algebra
of multiplicity types; that argument also avoids choosing an ordering of the finite alphabet, but
without loading the multivariate-polynomial coefficient environment. -/
theorem card_typeClass_eq_multinomial (a : ι → ℕ) (ha : a ∈ types ι n) :
    (typeClass n a).card = Nat.multinomial Finset.univ a :=
  card_typeClass_eq_multinomial_light a ha

/-- **Chain rule for multinomial coefficients.**  Over a product alphabet the multinomial
coefficient of a joint profile is the multinomial coefficient of its first marginal times the
product of the per-row multinomial coefficients.  The proof is division-free: it cancels the
common factorial product coming from `Nat.multinomial_spec`. -/
theorem multinomial_eq_multinomial_mappedType_fst_mul_prod
    {C : Type u} {F : Type v} [Fintype C] [Fintype F] (j : C × F → ℕ) :
    Nat.multinomial Finset.univ j =
      Nat.multinomial Finset.univ (mappedType Prod.fst j) *
        ∏ c, Nat.multinomial Finset.univ fun f ↦ j (c, f) := by
  classical
  have hw : ∀ c, mappedType Prod.fst j c = ∑ f, j (c, f) := by
    intro c
    simp only [mappedType, letterFiber, Finset.sum_filter]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
    · simp
    · intro other _ hother
      simp [hother]
    · simp
  have hsum : ∑ x : C × F, j x = ∑ c, mappedType Prod.fst j c := by
    simp only [hw]
    exact Fintype.sum_prod_type j
  have hfact : (∏ x : C × F, Nat.factorial (j x)) = ∏ c, ∏ f, Nat.factorial (j (c, f)) :=
    Fintype.prod_prod_type fun x ↦ Nat.factorial (j x)
  have h1 := Nat.multinomial_spec (Finset.univ : Finset (C × F)) j
  have h2 := Nat.multinomial_spec (Finset.univ : Finset C) (mappedType Prod.fst j)
  have h3 : ∀ c : C, (∏ f, Nat.factorial (j (c, f))) *
      Nat.multinomial Finset.univ (fun f ↦ j (c, f)) = Nat.factorial (mappedType Prod.fst j c) := by
    intro c
    rw [hw c]
    exact Nat.multinomial_spec (Finset.univ : Finset F) fun f ↦ j (c, f)
  have hpos : 0 < ∏ x : C × F, Nat.factorial (j x) :=
    Finset.prod_pos fun x _ ↦ Nat.factorial_pos _
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc
    (∏ x : C × F, Nat.factorial (j x)) * Nat.multinomial Finset.univ j
        = Nat.factorial (∑ x : C × F, j x) := h1
    _ = Nat.factorial (∑ c, mappedType Prod.fst j c) := by rw [hsum]
    _ = (∏ c, Nat.factorial (mappedType Prod.fst j c)) *
          Nat.multinomial Finset.univ (mappedType Prod.fst j) := h2.symm
    _ = (∏ c, ((∏ f, Nat.factorial (j (c, f))) *
            Nat.multinomial Finset.univ fun f ↦ j (c, f))) *
          Nat.multinomial Finset.univ (mappedType Prod.fst j) := by
        refine congrArg (· * Nat.multinomial Finset.univ (mappedType Prod.fst j)) ?_
        exact Finset.prod_congr rfl fun c _ ↦ (h3 c).symm
    _ = ((∏ c, ∏ f, Nat.factorial (j (c, f))) *
            ∏ c, Nat.multinomial Finset.univ fun f ↦ j (c, f)) *
          Nat.multinomial Finset.univ (mappedType Prod.fst j) := by
        rw [Finset.prod_mul_distrib]
    _ = (∏ x : C × F, Nat.factorial (j x)) *
          (Nat.multinomial Finset.univ (mappedType Prod.fst j) *
            ∏ c, Nat.multinomial Finset.univ fun f ↦ j (c, f)) := by
        rw [hfact]
        ring

/-- Every valid type is realized by at least one word. -/
theorem typeClass_nonempty (a : ι → ℕ) (ha : a ∈ types ι n) :
    (typeClass n a).Nonempty := by
  rw [← Finset.card_pos, card_typeClass_eq_multinomial a ha]
  exact Nat.multinomial_pos Finset.univ a

/-- Pushforward of finite multiplicity profiles is functorial. -/
theorem mappedType_comp {α β γ : Type*} [Fintype α] [Fintype β]
    (f : α → β) (g : β → γ) (a : α → ℕ) :
    mappedType g (mappedType f a) = mappedType (g ∘ f) a := by
  classical
  have ha : a ∈ types α (∑ i, a i) := by
    rw [mem_types]
  obtain ⟨word, hword⟩ := typeClass_nonempty a ha
  have hwordType : multiplicity word = a := mem_typeClass.mp hword
  rw [← hwordType, ← multiplicity_comp_eq_mappedType f word,
    ← multiplicity_comp_eq_mappedType g (f ∘ word),
    ← multiplicity_comp_eq_mappedType (g ∘ f) word]
  rfl

/-- There is at least one type whenever the alphabet is nonempty. -/
theorem types_nonempty (ι : Type u) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (types ι n).Nonempty := by
  classical
  let word : Fin n → ι := fun _ ↦ Classical.choice inferInstance
  exact ⟨multiplicity word, multiplicity_mem_types word⟩

/-- Weighted size of a multiplicity class. -/
noncomputable def weightedClassTerm (x : ι → ℝ) (n : ℕ) (a : ι → ℕ) : ℝ :=
  (typeClass n a).card * ∏ i, x i ^ a i

theorem weightedClassTerm_nonneg (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (n : ℕ) (a : ι → ℕ) :
    0 ≤ weightedClassTerm x n a := by
  unfold weightedClassTerm
  exact mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hx i) _)

/-- Some multiplicity type captures the full weighted word sum up to the polynomial number of
types.  This is the precise finite selection estimate used in Schönhage's equation (7.12). -/
theorem exists_type_large_weighted_term [Nonempty ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (n : ℕ) :
    ∃ a ∈ types ι n,
      (∑ i, x i) ^ n ≤
        ((n + 1) ^ Fintype.card ι : ℕ) * weightedClassTerm x n a := by
  classical
  obtain ⟨a, ha, hmax⟩ :=
    Finset.exists_max_image (types ι n) (weightedClassTerm x n) (types_nonempty ι n)
  refine ⟨a, ha, ?_⟩
  rw [pow_sum_eq_sum_type_class]
  change (∑ b ∈ types ι n, weightedClassTerm x n b) ≤ _
  calc
    (∑ b ∈ types ι n, weightedClassTerm x n b) ≤
        (types ι n).card • weightedClassTerm x n a :=
      Finset.sum_le_card_nsmul _ _ _ hmax
    _ = ((types ι n).card : ℝ) * weightedClassTerm x n a := by
      rw [nsmul_eq_mul]
    _ ≤ (((n + 1) ^ Fintype.card ι : ℕ) : ℝ) * weightedClassTerm x n a :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_types_le ι n)
        (weightedClassTerm_nonneg x hx n a)

end AlgebraicComplexity.WordType
