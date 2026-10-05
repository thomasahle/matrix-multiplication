/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Nat.Choose.Multinomial
import AlgebraicComplexity.Combinatorics.WordTypeCore

set_option autoImplicit false

/-!
# Lightweight exact cardinality of a word type class

The coefficient proof in the original omnibus `WordType` module used multivariate polynomials.
This file proves the same identity in the underlying additive monoid algebra.  It loads only the
convolution and multinomial interfaces needed for the argument, keeping exact type-class counting
available to memory-sensitive tensor clients.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u

variable {ι : Type u} [Fintype ι] {n : ℕ}

private abbrev TypeMonoidAlgebra (ι : Type u) :=
  AddMonoidAlgebra ℕ (ι →₀ ℕ)

private noncomputable def typeMonomial (i : ι) : TypeMonoidAlgebra ι :=
  AddMonoidAlgebra.single (Finsupp.single i 1) 1

private theorem prod_typeMonomial_word (word : Fin n → ι) :
    (∏ j, typeMonomial (word j)) =
      AddMonoidAlgebra.single
        (Finsupp.equivFunOnFinite.symm (multiplicity word)) 1 := by
  classical
  change (∏ j ∈ Finset.univ,
      AddMonoidAlgebra.single (Finsupp.single (word j) 1) 1) = _
  rw [AddMonoidAlgebra.prod_single]
  simp only [Finset.prod_const_one]
  congr 1
  apply Finsupp.ext
  intro i
  simp [multiplicity, Finsupp.single_apply]

private theorem prod_typeMonomial_profile (a : ι → ℕ) :
    (∏ i, typeMonomial i ^ a i) =
      AddMonoidAlgebra.single (Finsupp.equivFunOnFinite.symm a) 1 := by
  classical
  change (∏ i ∈ Finset.univ,
      AddMonoidAlgebra.single (Finsupp.single i 1) 1 ^ a i) = _
  simp only [AddMonoidAlgebra.single_pow, one_pow]
  rw [AddMonoidAlgebra.prod_single]
  simp only [Finset.prod_const_one]
  congr 1
  apply Finsupp.ext
  intro i
  simp [Finsupp.single_apply]

/-- The cardinality of an exact word type class is its multinomial coefficient.  This version uses
only an additive monoid algebra, rather than the substantially larger multivariate-polynomial
coefficient environment.

Proof sketch: expand the `n`th power of the sum of the letter monomials in two ways—once over words
and once by the multinomial theorem—and compare the coefficient of the monomial encoded by `a`.
The word expansion contributes one exactly for words of type `a`, while the multinomial expansion
contributes `Nat.multinomial Finset.univ a`; `ha` identifies the common total degree with `n`. -/
theorem card_typeClass_eq_multinomial_light (a : ι → ℕ) (ha : a ∈ types ι n) :
    (typeClass n a).card = Nat.multinomial Finset.univ a := by
  classical
  have hsum : ∑ i, a i = n := mem_types.mp ha
  let d : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm a
  let X : ι → TypeMonoidAlgebra ι := typeMonomial
  have hword := Fintype.sum_pow X n
  have hmultinomial :=
    Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset ι) X n
  have hexpansion :
      (∑ word : Fin n → ι, ∏ j, X (word j)) =
        ∑ b ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
          Nat.multinomial Finset.univ b * ∏ i ∈ Finset.univ, X i ^ b i :=
    hword.symm.trans hmultinomial
  have hcoeff := congrArg (fun p : TypeMonoidAlgebra ι ↦ p.coeff d) hexpansion
  simpa [X, d, typeClass, types, prod_typeMonomial_word,
    prod_typeMonomial_profile, Finsupp.single_apply,
    AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single, ha, hsum] using hcoeff

end AlgebraicComplexity.WordType
