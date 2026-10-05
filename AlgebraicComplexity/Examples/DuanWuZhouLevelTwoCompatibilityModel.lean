/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCopyCount

/-!
# The legwise compatibility model of `[DuanWuZhou2022]` section 6, and what it can retain

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoJointHashing.lean` leaves
the legwise source model `compat : ∀ leg : Leg, Fin 5 → CWSquareAddress → Prop` to the count lane,
because it is the choice whose isolated support `dwz63JointIsolatedSupport` carries the copy
count.  This module fixes that choice, proves its soundness, and then proves the *ceiling* it runs
into --- a ceiling that is a property of the signature, not of the choice.

## The model

`[DuanWuZhou2022]`'s compatibility (`global_value.tex`, `def:global-compatible`, and its
second-power form `second_power.tex`, `def:complv2`) says that a **small** (level-`ℓ-1`)
`Z`-block `Z_K̂ ∈ Z_K` is compatible with a **large** triple `(X_I, Y_J, Z_K)` when

1. for each `k`, `split(K̂, S_{*,*,k}) = α̃^avg_{*,*,k}`, and
2. for each large component `(i,j,k)` with `i = 0` or `j = 0`, `split(K̂, S_{i,j,k}) = α̃_{i,j,k}`,

where `S_{i,j,k} = {t | (I_t, J_t, K_t) = (i,j,k)}` is read off the large triple and `split` is the
*refinement* distribution of the small index inside the large one.

The Lean signature is letterwise: `symSixPowerCompatible compat pivot n` is built by
`positivePowerCompatible` (one letter at a time) out of `symSixCompatible` (one orientation at a
time) out of `compat leg`, which sees only *one coarse degree* `a : Fin 5` at the pivot leg and
*one coarse cell* `addr : CWSquareAddress`.  The paper's `split(K̂, ·)` is invisible at that
resolution: it is a statement about the level-`ℓ-1` refinement, which in this tree lives at the
`AvailableWord` / `SplitRestriction` layer that `dwz63_restricts_power_symSix_of_jointHash`'s
`holes` argument ranges over --- not at the block-address layer.  What survives the restriction to
this signature is condition 2's *shadow*: the pivot label must be the one the cell actually
carries.  That is `dwz63LabelCompat`, and `dwz63LabelCompat_maximal` shows it is the **strongest**
sound model expressible here, so nothing is lost by choosing it.

## The ceiling, and why it binds

`injOn_leg_of_compatibilityIsolated` --- the committed
`Tensor.compatibilityIsolatedSupport_hasUniqueLegFibers` read negatively, as in
`Tensor/CompatibilityIsolationCeiling.lean` --- says that for *every* sound model the surviving
addresses have pairwise distinct pivot labels.  At `pivot = .Z` that caps
`dwz63JointIsolatedSupport` by the number of **distinct `Z`-block words** the hash retained
(`card_dwz63JointIsolatedSupport_le_card_zWords`), uniformly in `compat`.

`dwz63_copyCount_forces_card_zWords` turns that into the statement a count-side client must face:
any `hcount` at loss `loss` forces

`dwz63TrueCopyRate ^ (6(n+1)) ≤ loss * #{distinct Z-words of the retained family}`.

The retained addresses come from `markedWords`, so if those are `dwz63Alpha`-typical --- which the
values lane requires --- every retained `Z`-word is a six-tuple of `dwz63AlphaZ`-typical words and
there are at most `exp(H_e(alpha_Z)) ^ (6(n+1))` of them up to a polynomial.  Numerically
`exp(H_e(alpha_Z)) = 2.9435358264` while `dwz63TrueCopyRate = 2.9718193767` (branch one, the
binding one), a ratio of `1.0096087` per oriented letter and `1.0590550` per position, so no
`Growth.Subexponential` loss can close it.

This is not a gap in the count lane's argument; it is a mismatch between where this tree performs
the `Z` cleanup and where `[DuanWuZhou2022]` performs it.  The paper's retained triples **do**
share large `Z`-blocks (`global_value.tex` Step 3: "those retained triples can only share
Z-blocks"), and the compatibility zero-out deletes *small* blocks inside them, leaving **holes**
that `hole_lemma.tex` then repairs --- it never deletes a copy.  Running
`Tensor.compatibilityIsolatedSupport` on the block-address family models "delete every copy whose
`Z`-block is shared", which is strictly stronger and is exactly what the ceiling forbids.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, sections 4.3 and 6 (`second_power.tex` `def:complv2`,
`global_value.tex` `def:global-compatible`, Additional Zeroing-Out Steps 1 and 2).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v w

/-! ## The model -/

/-- **The section 6 legwise compatibility model, at the resolution the signature allows.**

A coarse degree `a` at leg `leg` is compatible with a coarse cell `addr` exactly when `addr`
carries `a` at that leg.  This is the block-address shadow of `def:global-compatible`'s condition
on `split(K̂, S_{i,j,k})`: the refinement itself is invisible here, and what remains is that the
cell must be the one the label names. -/
def dwz63LabelCompat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop :=
  fun leg a addr ↦ addr leg = a

@[simp] theorem dwz63LabelCompat_iff (leg : Leg) (a : Fin 5) (addr : CWSquareAddress) :
    dwz63LabelCompat leg a addr ↔ addr leg = a := Iff.rfl

/-- **`hcompat`.**  Soundness is reflexivity: every coarse address carries its own label. -/
theorem dwz63LabelCompat_sound (K : Type u) [CommRing K] (leg : Leg) :
    IsCompatibilitySound (cwSquarePartitionedTensor K dwz63Q).support leg
      (dwz63LabelCompat leg) :=
  fun _ _ ↦ rfl

/-- **`hcompat`, in the `∀ leg` shape the assembly consumes.** -/
theorem dwz63LabelCompat_sound_forall (K : Type u) [CommRing K] :
    ∀ leg : Leg, IsCompatibilitySound (cwSquarePartitionedTensor K dwz63Q).support leg
      (dwz63LabelCompat leg) :=
  dwz63LabelCompat_sound K

/-! ## Anti-vacuity: the model is a strict refinement -/

/-- **No cell is compatible with two different degrees at the same leg.**  In particular the
compatible set of a label is a proper subset of the support --- the model is not `fun _ _ ↦ True`,
which is sound and retains nothing. -/
theorem dwz63LabelCompat_not_two (leg : Leg) (addr : CWSquareAddress) {a b : Fin 5} (hab : a ≠ b) :
    ¬(dwz63LabelCompat leg a addr ∧ dwz63LabelCompat leg b addr) := by
  rintro ⟨ha, hb⟩
  exact hab (ha.symm.trans hb)

/-- **Strictness, concretely**: no address is compatible with every degree. -/
theorem not_forall_dwz63LabelCompat (leg : Leg) (addr : CWSquareAddress) :
    ¬ ∀ a : Fin 5, dwz63LabelCompat leg a addr := by
  intro h
  exact dwz63LabelCompat_not_two leg addr (a := 0) (b := 1) (by decide) ⟨h 0, h 1⟩

/-! ## The model is the strongest sound one -/

section Maximal

variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- **Every sound model is contained in label equality.**  Soundness makes an address compatible
with its own label, so a compatible pair with equal labels is forced --- there is no sound model
that separates two addresses carrying the same pivot label. -/
theorem sound_compatible_of_leg_eq
    {ambient : Finset (BlockAddress A)} {pivot : Leg}
    {compatible : A pivot → BlockAddress A → Prop}
    (hsound : IsCompatibilitySound ambient pivot compatible)
    {address other : BlockAddress A} (hother : other ∈ ambient)
    (hlabel : other pivot = address pivot) : compatible (address pivot) other := by
  rw [← hlabel]
  exact hsound other hother

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- **The ceiling, as injectivity.**  For every sound model the addresses that survive the
compatibility cleanup have pairwise distinct pivot labels.  This is
`Tensor/CompatibilityIsolationCeiling.lean`'s statement in the form a counting client uses, proved
here from `Tensor.compatibilityIsolatedSupport_hasUniqueLegFibers` so that no extra import is
needed. -/
theorem injOn_leg_of_compatibilityIsolated
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hsound : IsCompatibilitySound ambient pivot compatible) :
    Set.InjOn (fun a : BlockAddress A ↦ a pivot)
      (compatibilityIsolatedSupport ambient pivot compatible : Set (BlockAddress A)) := by
  classical
  have hunique :=
    compatibilityIsolatedSupport_hasUniqueLegFibers ambient pivot compatible hsound
  intro left hleft right hright hlabel
  exact hunique.2 right (by simpa using hright) left (hunique.1 (by simpa using hleft)) hlabel

omit [∀ c, Fintype (A c)] in
/-- **The counting form of the ceiling.**  The isolated support injects into the ambient's set of
pivot labels, uniformly in the compatibility relation. -/
theorem card_compatibilityIsolatedSupport_le_card_image
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hsound : IsCompatibilitySound ambient pivot compatible) :
    (compatibilityIsolatedSupport ambient pivot compatible).card ≤
      (ambient.image fun a ↦ a pivot).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun a ↦ a pivot) ?_ ?_
  · intro a ha
    exact Finset.mem_image_of_mem _
      (compatibilityIsolatedSupport_subset ambient pivot compatible ha)
  · exact injOn_leg_of_compatibilityIsolated ambient pivot compatible hsound

end Maximal

/-! ## The ceiling at the level-two instance -/

section Instance

variable {R : Type v} [Field R] {p : ℕ} [CharP R p]

/-- **The doubly isolated support is capped by the number of distinct retained `Z`-block words**,
uniformly in the legwise model `compat`.

Both compatibility zero-outs are sound for any legwise source model --- that is the hashing
module's `isCompatibilitySound_symSixPowerCompatible_of_subset` composed with
`isCompatibilitySound_compatibilityIsolatedSupport` --- so the `Z` stage's survivors have pairwise
distinct `Z` words, and they all come from the family the hash retained. -/
theorem card_dwz63JointIsolatedSupport_le_card_zWords [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (hcompat : ∀ leg : Leg,
      IsCompatibilitySound (cwSquarePartitionedTensor K dwz63Q).support leg (compat leg)) :
    (dwz63JointIsolatedSupport K hp n markedWords B seed compat).card ≤
      ((dwz63JointRetainedSupport K hp n markedWords B seed).image
        fun a ↦ a .Z).card := by
  classical
  have hsubset := dwz63JointRetainedSupport_subset K hp n markedWords B seed
  have hsoundZ :
      IsCompatibilitySound
        (compatibilityIsolatedSupport (dwz63JointRetainedSupport K hp n markedWords B seed) .Y
          (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n)) .Z
        (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n) :=
    isCompatibilitySound_compatibilityIsolatedSupport
      (isCompatibilitySound_symSixPowerCompatible_of_subset
        (cwSquarePartitionedTensor K dwz63Q) compat .Z n hsubset hcompat)
  have hcap := card_compatibilityIsolatedSupport_le_card_image
    (compatibilityIsolatedSupport (dwz63JointRetainedSupport K hp n markedWords B seed) .Y
      (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n)) .Z
    (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n) hsoundZ
  refine hcap.trans (Finset.card_le_card (Finset.image_subset_image ?_))
  exact compatibilityIsolatedSupport_subset _ _ _

/-- **What any `hcount` forces.**

A copy count at subexponential loss is, by the ceiling, a count of *distinct retained `Z`-block
words*.  Since the retained addresses come from `markedWords`, a `dwz63Alpha`-typical marked
family supplies at most `exp(H_e(alpha_Z)) ^ (6(n+1))` of them up to a polynomial, while
`dwz63TrueCopyRate = 2.9718193767 > 2.9435358264 = exp(H_e(alpha_Z))`.  So this consequence is the
place the current placement of the `Z` cleanup has to be repaired. -/
theorem dwz63_copyCount_forces_card_zWords [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (hcompat : ∀ leg : Leg,
      IsCompatibilitySound (cwSquarePartitionedTensor K dwz63Q).support leg (compat leg))
    {loss : ℝ} (hloss : 0 ≤ loss)
    (hcount : dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      loss * ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ)) :
    dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      loss * (((dwz63JointRetainedSupport K hp n markedWords B seed).image
        fun a ↦ a .Z).card : ℝ) := by
  refine hcount.trans (mul_le_mul_of_nonneg_left ?_ hloss)
  exact_mod_cast card_dwz63JointIsolatedSupport_le_card_zWords K hp n markedWords B seed compat
    hcompat

/-! ## The same ceiling, upstream of every compatibility choice -/

/-- **The retained family is counted by its `X`-block words.**  `dwz63_x_injOn_jointRetained` is
already committed, so this is an equality, not a bound --- and it holds *before* any compatibility
zero-out, hence for every legwise model. -/
theorem card_image_x_dwz63JointRetainedSupport [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    ((dwz63JointRetainedSupport K hp n markedWords B seed).image fun a ↦ a .X).card =
      (dwz63JointRetainedSupport K hp n markedWords B seed).card :=
  Finset.card_image_of_injOn (dwz63_x_injOn_jointRetained K hp n markedWords B hB seed)

/-- **Any copy count is a count of distinct `X`-block words.**

The two compatibility zero-outs only shrink the family, so `hcount` already forces the retained
`X`-words to be that numerous --- no property of `compat` is used, and the `Y`/`Z` budgets cannot
help.  A `dwz63Alpha`-typical marked family supplies `X`-words whose six orientation components
have marginal types `dwz63AlphaX` four times and `dwz63AlphaZ` twice --- every target leg reads
every source leg exactly twice, since the six orientations are all of `Equiv.Perm Leg` --- so
there are at most `(exp(H_e(alpha_X)) ^ 4 * exp(H_e(alpha_Z)) ^ 2) ^ (n+1)` of them up to a
polynomial: `675.8157245 ^ (n+1)`, against a demand of
`dwz63TrueCopyRate ^ (6(n+1)) = 688.8655403 ^ (n+1)`.

The `1.0193097` per-position gap is exponential, so this inequality is unsatisfiable with
`Growth.Subexponential` loss.  It is the `6N` normalization hazard `PREP.md` section 4.4 flags
("**This normalization must be re-derived, not copied**"): the honest product of the six regional
minima is `∏_e min(alphabar_{e⁻¹X} / K, alphabar_{e⁻¹Z} / alphabar_p) = alphabar_X ^ 4 *
alphabar_Z ^ 2`, not `min(alphabar_X / K, alphabar_Z / alphabar_p) ^ 6`, and the two differ
exactly because `alphabar_X ≠ alphabar_Z`. -/
theorem dwz63_copyCount_forces_card_xWords [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    {loss : ℝ} (hloss : 0 ≤ loss)
    (hcount : dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      loss * ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ)) :
    dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      loss * (((dwz63JointRetainedSupport K hp n markedWords B seed).image
        fun a ↦ a .X).card : ℝ) := by
  refine hcount.trans (mul_le_mul_of_nonneg_left ?_ hloss)
  have hsub : (dwz63JointIsolatedSupport K hp n markedWords B seed compat).card ≤
      (dwz63JointRetainedSupport K hp n markedWords B seed).card := by
    refine Finset.card_le_card ((compatibilityIsolatedSupport_subset _ _ _).trans ?_)
    exact compatibilityIsolatedSupport_subset _ _ _
  rw [card_image_x_dwz63JointRetainedSupport K hp n markedWords B hB seed]
  exact_mod_cast hsub

end Instance

end AlgebraicComplexity.Examples
