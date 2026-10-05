/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore

/-!
# Exact cellwise multinomial counts

For a fixed source word, a legal joint type with the prescribed source marginal has exactly the
product of its row multinomials many conditional words. The law-facing restatement derives joint
legality and the source marginal from the row masses.

This is the finite cellwise count used in Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication* [alman2025more], Claim 6.18
(`papers/sources/2404.16349/constituent.tex:406-436`), and in the finite step of
`better_bound/paper.tex`, Theorem `thm:reader-indexed-parent-type`. The source fixes the coarse
word, partitions its positions by compatibility cells, and counts the fine words independently
inside each cell. The exact formula here precedes its entropy estimate.

Proof sketch: double-count the joint type class to obtain the source multinomial times the
conditional count. Apply the product-alphabet multinomial chain rule and cancel the positive
source multinomial. Both operations are finite and division-free; no entropy, Stirling bound,
reader-model instantiation, tensor extraction, or numerical certificate is used.

The declarations are re-exported by `IdentityOrientationCompetitorCount`; this finite leaf lets
exact counting clients avoid that module's asymptotic import closure.
-/

set_option autoImplicit false

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v w

section Product

variable {C : Type u} {F : Type v} [Fintype C] [Fintype F]

/-- **The loss-free cellwise competitor count.**  For a fixed coarse word `source` -- the fixed
coarse split sequence of the certificate -- the compatible fine words are counted *exactly* by
the product over compatibility cells of the per-cell multinomial coefficient.  This is the
Claim-6.18 bound with no `± o(n)`. -/
theorem card_conditionalTypeClass_eq_prod_multinomial
    {n : ℕ} (source : Fin n → C) (jointType : C × F → ℕ)
    (hjoint : jointType ∈ types (C × F) n)
    (hmap : mappedType Prod.fst jointType = multiplicity source) :
    (conditionalTypeClass source jointType).card =
      ∏ c, Nat.multinomial Finset.univ fun f ↦ jointType (c, f) := by
  have hfactor :=
    multinomial_source_mul_card_conditionalTypeClass source jointType hjoint hmap
  rw [multinomial_eq_multinomial_mappedType_fst_mul_prod jointType, hmap] at hfactor
  exact Nat.eq_of_mul_eq_mul_left (Nat.multinomial_pos _ _) hfactor

/-- Certificate-facing restatement: the compatibility data is a table of *per-cell laws* `law c`,
each of total mass the number of coordinates the fixed coarse word puts in cell `c`.  No legality
or marginal side condition is left for the client. -/
theorem card_conditionalTypeClass_eq_prod_multinomial_of_law
    {n : ℕ} (source : Fin n → C) (law : C → F → ℕ)
    (hlaw : ∀ c, ∑ f, law c f = multiplicity source c) :
    (conditionalTypeClass source fun x ↦ law x.1 x.2).card =
      ∏ c, Nat.multinomial Finset.univ (law c) := by
  classical
  have hmap : mappedType Prod.fst (fun x : C × F ↦ law x.1 x.2) = multiplicity source := by
    funext c
    rw [mappedType_fst_apply]
    exact hlaw c
  have hjoint : (fun x : C × F ↦ law x.1 x.2) ∈ types (C × F) n := by
    rw [mem_types]
    calc
      ∑ x : C × F, law x.1 x.2 = ∑ c, ∑ f, law c f := Fintype.sum_prod_type _
      _ = ∑ c, multiplicity source c := Finset.sum_congr rfl fun c _ ↦ hlaw c
      _ = n := sum_multiplicity source
  exact card_conditionalTypeClass_eq_prod_multinomial source _ hjoint hmap

end Product

end AlgebraicComplexity.WordType
