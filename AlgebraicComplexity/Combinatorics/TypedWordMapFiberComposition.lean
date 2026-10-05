/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType

set_option autoImplicit false

/-!
# Disintegration of typed word-map fibers

For maps of finite alphabets `A → B → C`, a typed lift of a `C`-word has a unique intermediate
`B`-word.  This module records the resulting exact equivalence

```text
typed lifts through (g ∘ f)
  ≃ Σ intermediate typed g-lifts, typed f-lifts of that intermediate word
```

and the corresponding cardinality identity.  The statement is pure finite combinatorics: it uses
only multiplicity profiles and coordinatewise maps, with no tensor, hashing, entropy, or
paper-specific alphabet.

The identity is the finite disintegration underlying the staged competitor accounting in the
Total-Weight manuscript's quotient-feature counting condition (`hyp:quotient-count` in
`better_bound/paper.tex:1729-1761`).  In that application, `f` remembers the ordered level-2
total-weight payload and `g` forgets its inner lift.  This module deliberately proves only the
generic exact identity; identifying its two stages with the certificate's level-3 and level-2
counts remains a client obligation.  The same disintegration principle is implicit in the
conditional-type counting used by [alman2025more].
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u v w

/-- Typed lifts through a composite map are exactly typed lifts through its two stages.

For `f : A → B`, `g : B → C`, source profile `a`, and target word `z`, the intermediate word
of a composite lift `x` is forced to be `f ∘ x`.  Its type is the pushed profile `mappedType f a`.
Conversely, an intermediate typed `g`-lift together with a typed `f`-lift of it determines a
composite lift by forgetting the intermediate word.

Proof sketch: map a composite lift `x` to the dependent pair `(f ∘ x, x)`.  The mapped-type lemma
identifies the multiplicity of `f ∘ x`, and associativity of coordinatewise composition gives the
outer target equation.  The inverse forgets the intermediate word; the inner and outer target
equations compose pointwise.  The two maps are inverse because the inner fiber equation uniquely
determines the intermediate word. -/
noncomputable def typedWordMapFiberCompEquiv
    {A : Type u} {B : Type v} {C : Type w} [Fintype A] [Fintype B]
    {n : ℕ} (f : A → B) (g : B → C) (a : A → ℕ) (target : Fin n → C) :
    {word // word ∈ typedWordMapFiber (g ∘ f) a target} ≃
      Σ middle : {middle //
          middle ∈ typedWordMapFiber g (mappedType f a) target},
        {word // word ∈ typedWordMapFiber f a middle.1} where
  toFun word := by
    have hword := mem_typedWordMapFiber.mp word.2
    refine ⟨⟨f ∘ word.1, ?_⟩, ⟨word.1, ?_⟩⟩
    · rw [mem_typedWordMapFiber]
      refine ⟨?_, ?_⟩
      · rw [multiplicity_comp_eq_mappedType, hword.1]
      · funext i
        exact congrFun hword.2 i
    · rw [mem_typedWordMapFiber]
      exact ⟨hword.1, rfl⟩
  invFun pair := by
    have hmiddle := mem_typedWordMapFiber.mp pair.1.2
    have hword := mem_typedWordMapFiber.mp pair.2.2
    refine ⟨pair.2.1, ?_⟩
    rw [mem_typedWordMapFiber]
    refine ⟨hword.1, ?_⟩
    funext i
    calc
      g (f (pair.2.1 i)) = g (pair.1.1 i) := congrArg g (congrFun hword.2 i)
      _ = target i := congrFun hmiddle.2 i
  left_inv word := by
    apply Subtype.ext
    rfl
  right_inv pair := by
    rcases pair with ⟨⟨middle, houter⟩, ⟨word, hword⟩⟩
    have hmiddle : (f ∘ word) = middle :=
      (mem_typedWordMapFiber.mp hword).2
    cases hmiddle
    rfl

/-- The cardinality of a typed fiber through `g ∘ f` is the sum of the inner typed-fiber
cardinalities over all admissible intermediate words.

This is the division-free finite chain rule for typed word-map fibers.  It is an equality, not an
upper bound: intermediate words partition the composite fiber without overlap.

Proof sketch: take cardinalities in `typedWordMapFiberCompEquiv`, use the cardinality formula for a
dependent sum, and rewrite subtype cardinalities as the cardinalities of their defining finite
sets. -/
theorem card_typedWordMapFiber_comp_eq_sum
    {A : Type u} {B : Type v} {C : Type w} [Fintype A] [Fintype B]
    {n : ℕ} (f : A → B) (g : B → C) (a : A → ℕ) (target : Fin n → C) :
    (typedWordMapFiber (g ∘ f) a target).card =
      ∑ middle ∈ typedWordMapFiber g (mappedType f a) target,
        (typedWordMapFiber f a middle).card := by
  classical
  rw [← Fintype.card_coe (typedWordMapFiber (g ∘ f) a target),
    Fintype.card_congr (typedWordMapFiberCompEquiv f g a target),
    Fintype.card_sigma]
  simp only [Fintype.card_coe]
  exact (Finset.sum_subtype
    (typedWordMapFiber g (mappedType f a) target) (fun _ ↦ Iff.rfl)
    (fun middle ↦ (typedWordMapFiber f a middle).card)).symm

end AlgebraicComplexity.WordType
