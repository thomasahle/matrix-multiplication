/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Basic

/-!
# Word transporters over an arbitrary finite position domain

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  The Hole Lemma of

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, §5 (`hole_lemma.tex`) (`[duan2023faster]`)

needs exactly three facts about position shuffling: two words with the same letter multiplicities
differ by a permutation of positions, the permutations carrying one word to another form a
translate of the stabilizer, and hence the transporter's size does not depend on the target.
`Combinatorics/ShufflingGroup.lean:271-299` and `Combinatorics/WordType.lean:217-231` carry all
three for the position domain `Fin n`.

`[duan2023faster]`'s shuffling group `Sym[n_1] x ... x Sym[n_m]` (`hole_lemma.tex:72-74`) acts on
the *fibres of a segmentation*, `{i // seg i = t}`, and not on a `Fin n`.  A segmented client must
therefore either transport every fibre to a `Fin` --- which destroys the definitional grip on the
action that its consumers rely on --- or restate the three facts over an arbitrary finite domain.
This module does the latter.

No mathematics is added.  `Equiv.ofFiberEquiv` (`Mathlib/Logic/Equiv/Basic.lean:191`) is already
stated for arbitrary types, and the transporter/stabilizer translation is `Equiv.Perm`
bookkeeping that never mentions the domain.  The committed `Fin n` forms are instances:
`WordShuffle.transporter` is `domainTransporter` by `rfl`, and
`WordType.positionPermOfSameMultiplicity`'s hypothesis is this one through
`WordType.multiplicity_eq_card_fiber`.

The paper computes the common transporter size as `∏_t ∏_{k'} (α̃_t(k') n_t)!`
(`hole_lemma.tex:116`).  As in the committed pooled case only its independence of the target is
used, so no factorial appears here.
-/

set_option autoImplicit false

namespace AlgebraicComplexity

namespace WordShuffle

universe u v

variable {D : Type u} [Fintype D] {I : Type v} [DecidableEq I]

/-- **Two words over the same finite domain whose letter fibres have equal size differ by a
permutation of positions.**  The domain-general form of
`WordType.positionPermOfSameMultiplicity` (`Combinatorics/WordType.lean:217`), whose hypothesis
`multiplicity left = multiplicity right` is this one through
`WordType.multiplicity_eq_card_fiber`. -/
noncomputable def domainPermOfSameFiberCard (left right : D → I)
    (h : ∀ a : I, Fintype.card {i // left i = a} = Fintype.card {i // right i = a}) :
    Equiv.Perm D :=
  Equiv.ofFiberEquiv (f := left) (g := right) fun a ↦ Fintype.equivOfCardEq (h a)

/-- The chosen permutation carries `right` back to `left`. -/
theorem domainPermOfSameFiberCard_map (left right : D → I)
    (h : ∀ a : I, Fintype.card {i // left i = a} = Fintype.card {i // right i = a}) :
    right ∘ domainPermOfSameFiberCard left right h = left := by
  funext i
  exact Equiv.ofFiberEquiv_map _ i

section Transporter

variable [DecidableEq D]

/-- **The permutations of the position domain carrying the word `v` to the word `w`.**  The
domain-general form of `WordShuffle.transporter` (`Combinatorics/ShufflingGroup.lean:271`), which
it equals by `rfl` at `D = Fin n`. -/
def domainTransporter (v w : D → I) : Finset (Equiv.Perm D) :=
  Finset.univ.filter fun π ↦ v ∘ π = w

@[simp] theorem mem_domainTransporter {v w : D → I} {π : Equiv.Perm D} :
    π ∈ domainTransporter v w ↔ v ∘ π = w := by
  simp [domainTransporter]

/-- **The transporter of a fixed source word has a size independent of its target.**

Proof sketch: right translation by a chosen transporting permutation `ρ` is a bijection from the
stabilizer `domainTransporter v v` onto `domainTransporter v w`.  This is the only group-theoretic
input the Hole Lemma needs; the paper instead computes the common size as a product of
factorials. -/
theorem card_domainTransporter_eq_card_stabilizer (v w : D → I)
    (ρ : Equiv.Perm D) (hρ : v ∘ ρ = w) :
    (domainTransporter v w).card = (domainTransporter v v).card := by
  refine Finset.card_nbij' (fun μ ↦ ρ.symm.trans μ) (fun π ↦ ρ.trans π) ?_ ?_ ?_ ?_
  · intro μ hμ
    rw [Finset.mem_coe, mem_domainTransporter] at hμ
    rw [Finset.mem_coe, mem_domainTransporter]
    funext i
    have h1 : v (μ (ρ.symm i)) = w (ρ.symm i) := congrFun hμ (ρ.symm i)
    have h2 : v (ρ (ρ.symm i)) = w (ρ.symm i) := congrFun hρ (ρ.symm i)
    rw [Equiv.apply_symm_apply] at h2
    simpa [Equiv.trans_apply] using h1.trans h2.symm
  · intro π hπ
    rw [Finset.mem_coe, mem_domainTransporter] at hπ
    rw [Finset.mem_coe, mem_domainTransporter]
    funext i
    have h1 : v (π (ρ i)) = v (ρ i) := congrFun hπ (ρ i)
    have h2 : v (ρ i) = w i := congrFun hρ i
    simpa [Equiv.trans_apply] using h1.trans h2
  · intro μ _
    apply Equiv.ext
    intro i
    simp [Equiv.trans_apply]
  · intro π _
    apply Equiv.ext
    intro i
    simp [Equiv.trans_apply]

end Transporter

end WordShuffle

end AlgebraicComplexity
