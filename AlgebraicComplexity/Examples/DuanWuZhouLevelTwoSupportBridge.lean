/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareCounting

/-!
# The section 6.3 support bridge: fifteen components as coarsened square addresses

`Examples/DuanWuZhouLevelTwoCounting.lean` records `[DuanWuZhou2022]`'s level-two distribution as
a bare fifteen-entry profile `dwz63Alpha : Fin 15 → ℕ` together with three coordinate readings
`dwz63XIndex`, `dwz63YIndex`, `dwz63ZIndex`.  Nothing there says that the fifteen abstract letters
*are* the fifteen supported addresses of the coarsened Coppersmith--Winograd square, so no tensor
statement can yet be made about them.  This module supplies that identification and transports the
counting-side families across it.

## The bijection

`dwz63Cell` reads a component's three coordinates off `dwz63{X,Y,Z}Index` and assembles the coarse
square address `ofLegs i j k`.  Every such address is supported, because `cwSquareSupport` is the
degree-four antidiagonal and `i + j + k = 4` holds cell by cell, and `dwz63CellIndex` inverts the
assembly by the explicit lexicographic offset table `![0, 5, 9, 12, 14]`.  A left inverse gives
injectivity, and `Fintype.card CWSquareSupport = 15` upgrades it to the bijection

`dwz63CellEquiv : Fin 15 ≃ CWSquareSupport`.

The three coordinate lemmas `dwz63CellEquiv_X/Y/Z` then hold *by `rfl`*: this is the precise sense
in which section 6.3's table order and `cwSquareAntidiagonal`'s listing order agree.  Because they
are definitional, no support-classification theorem is needed anywhere downstream.

## What is transported

`dwz63WordEquiv` carries a word `Fin (depth + 1) → Fin 15` to the recursive representation
`PositiveWord CWSquareSupport depth` used by `MatrixMultiplication/PartitionedPowerHashing.lean`.
Along it,

* `dwz63TripleSet` --- the three-marginal ambient family of `[DuanWuZhou2022]`'s `N_triple` ---
  becomes exactly `dwz63AmbientWords`, the family selected by three legwise multiplicity
  conditions on `PartitionHashEncoding.supportWordAddress`, i.e. by legwise block zeroing
  (`mem_dwz63AmbientWords_dwz63WordEquiv`, `card_dwz63AmbientWords`);
* the exact fifteen-cell type class becomes the positive type class `dwz63MarkedWords`
  (`mem_dwz63MarkedWords_dwz63WordEquiv`, `card_dwz63MarkedWords`);
* marked is contained in ambient (`dwz63MarkedWords_subset_ambientWords`), and at the section 6.3
  data this is discharged by the committed marginal identities of `M-DWZ9`
  (`dwz63MarkedWords_subset_ambientWords_proportional`).

`dwz63AmbientWords_reindex_mem_iff` records that the ambient family is stable under a simultaneous
permutation of word positions, which is the hypothesis
`PartitionHashEncoding.card_sourceWordLegFiber_eq_of_multiplicity_eq` consumes when a hashing
client needs equal ambient leg fibers.

## Hashing model

No new hashing model is introduced.  `cwSquarePartitionHashEncoding` already encodes each leg by
its `Fin 5` degree with target `4`, and `cwSquareAntidiagonal_degree_sum` is its legality proof;
`dwz63PartitionHashEncoding` is that encoding read through the bridge.  Its one field hypothesis is
that the five degree labels stay distinct in the coefficient field, which a client discharges by
choosing a modulus at least five.

Deliberately **not** reused: `cwSquareAmbientWords` and `cwSquareMarkedWords`.  Those are
specialised to the orbit-symmetric four-parameter profile `cwSquareNaturalType a b c d k`, whereas
section 6.3's fifteen-entry `dwz63Alpha` is asymmetric, so the ambient family here carries three
independent five-letter marginals rather than one.

## Position in the library

Layer 4 (a client).  It defines no tensor, proves no new counting theorem, and introduces no
hypothesis: everything is an identification of committed section 6.3 data with committed
Coppersmith--Winograd square data.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3 and `table:result-2nd`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

noncomputable section

/-! ## Pushforward along a bijection of alphabets -/

/-- Pushing a multiplicity profile forward along a bijection just relabels it. -/
theorem mappedType_equiv {A B : Type*} [Fintype A] (e : A ≃ B) (a : A → ℕ) :
    WordType.mappedType (e : A → B) a = fun b ↦ a (e.symm b) := by
  classical
  funext b
  have hfiber : WordType.letterFiber (e : A → B) b = {e.symm b} := by
    ext x
    simp [WordType.mem_letterFiber, Equiv.apply_eq_iff_eq_symm_apply]
  show ∑ x ∈ WordType.letterFiber (e : A → B) b, a x = a (e.symm b)
  rw [hfiber, Finset.sum_singleton]

/-- Relabelling a multiplicity profile along a bijection loses no information. -/
theorem mappedType_equiv_injective {A B : Type*} [Fintype A] (e : A ≃ B) :
    Function.Injective (WordType.mappedType (e : A → B)) := by
  intro a b h
  rw [mappedType_equiv, mappedType_equiv] at h
  funext x
  simpa using congrFun h (e x)

/-! ## The fifteen section 6.3 components as coarsened square addresses -/

/-- The coarse square address of section 6.3's `c`-th component, assembled from its three
recorded coordinates. -/
def dwz63Cell (c : Fin 15) : CWSquareAddress :=
  cwSquareAddress (dwz63XIndex c) (dwz63YIndex c) (dwz63ZIndex c)

/-- Every section 6.3 component lies on the degree-four antidiagonal, hence in the coarsened
square support. -/
theorem dwz63Cell_mem_cwSquareSupport (c : Fin 15) : dwz63Cell c ∈ cwSquareSupport := by
  rw [cwSquareSupport_eq_antidiagonal]
  fin_cases c <;> decide

/-- Position of a coarse square address in section 6.3's lexicographic listing.  The offsets
`![0, 5, 9, 12, 14]` are the starting positions of the blocks `i = 0, 1, 2, 3, 4`; the truncation
keeps the function total on unsupported addresses, where its value is irrelevant. -/
def dwz63CellIndex (s : CWSquareAddress) : Fin 15 :=
  ⟨min 14 (![0, 5, 9, 12, 14] (s .X) + (s .Y).val), by omega⟩

@[simp] theorem dwz63CellIndex_dwz63Cell (c : Fin 15) : dwz63CellIndex (dwz63Cell c) = c := by
  fin_cases c <;> rfl

theorem dwz63Cell_injective : Function.Injective dwz63Cell :=
  Function.LeftInverse.injective dwz63CellIndex_dwz63Cell

/-- **The section 6.3 alphabet is the coarsened square support.**  The fifteen components of
`table:result-2nd`, in the paper's own lexicographic order, are exactly the fifteen addresses of
`cwSquareAntidiagonal`, in that same order. -/
def dwz63CellEquiv : Fin 15 ≃ CWSquareSupport :=
  Equiv.ofBijective
    (fun c ↦ (⟨dwz63Cell c, dwz63Cell_mem_cwSquareSupport c⟩ : CWSquareSupport))
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun _ _ h ↦ dwz63Cell_injective (congrArg Subtype.val h), by
        rw [Fintype.card_fin, Fintype.card_coe, card_cwSquareSupport]⟩)

@[simp] theorem dwz63CellEquiv_coe (c : Fin 15) :
    ((dwz63CellEquiv c : CWSquareSupport) : CWSquareAddress) = dwz63Cell c := rfl

/-- The `X` coordinate of a transported component is `[DuanWuZhou2022]`'s `i`. -/
theorem dwz63CellEquiv_X (c : Fin 15) :
    ((dwz63CellEquiv c : CWSquareSupport) : CWSquareAddress) .X = dwz63XIndex c := rfl

/-- The `Y` coordinate of a transported component is `[DuanWuZhou2022]`'s `j`. -/
theorem dwz63CellEquiv_Y (c : Fin 15) :
    ((dwz63CellEquiv c : CWSquareSupport) : CWSquareAddress) .Y = dwz63YIndex c := rfl

/-- The `Z` coordinate of a transported component is `[DuanWuZhou2022]`'s `k`. -/
theorem dwz63CellEquiv_Z (c : Fin 15) :
    ((dwz63CellEquiv c : CWSquareSupport) : CWSquareAddress) .Z = dwz63ZIndex c := rfl

/-- The three coordinate readings of section 6.3's components, bundled by tensor leg. -/
def dwz63LegIndex : Leg → Fin 15 → Fin 5
  | .X => dwz63XIndex
  | .Y => dwz63YIndex
  | .Z => dwz63ZIndex

/-- Reading one leg of a transported component is the corresponding section 6.3 coordinate. -/
theorem dwz63LegIndex_comp_cellEquiv (c : Leg) :
    (fun s : CWSquareSupport ↦ (s : CWSquareAddress) c) ∘ (dwz63CellEquiv : Fin 15 → _) =
      dwz63LegIndex c := by
  funext i
  cases c <;> rfl

/-- Pushing a fifteen-cell profile to one leg through the bridge is the corresponding section 6.3
coordinate marginal. -/
theorem mappedType_legProj_cellEquiv (c : Leg) (a : Fin 15 → ℕ) :
    WordType.mappedType (fun s : CWSquareSupport ↦ (s : CWSquareAddress) c)
        (WordType.mappedType (dwz63CellEquiv : Fin 15 → CWSquareSupport) a) =
      WordType.mappedType (dwz63LegIndex c) a := by
  rw [WordType.mappedType_comp, dwz63LegIndex_comp_cellEquiv]

/-! ## The hashing model -/

/-- **Section 6.3's affine hashing model is the committed square encoding.**  Each leg is encoded
by its `Fin 5` degree and the constant target is `4`; legality is
`cwSquareAntidiagonal_degree_sum`.  The single field hypothesis is that the five degree labels
remain distinct, which a finite-field client discharges by choosing a modulus at least five. -/
def dwz63PartitionHashEncoding {R : Type*} [Field R]
    (hinjective : Function.Injective (cwSquareFieldValue (R := R))) :
    PartitionHashEncoding (R := R) cwSquareSupport :=
  cwSquarePartitionHashEncoding hinjective

/-! ## Transport of words -/

/-- Transport a section 6.3 word into the recursive square-support word representation used by the
partitioned-power hashing API. -/
def dwz63WordEquiv (depth : ℕ) :
    (Fin (depth + 1) → Fin 15) ≃ PositiveWord CWSquareSupport depth :=
  (Equiv.arrowCongr (Equiv.refl (Fin (depth + 1))) dwz63CellEquiv).trans
    (positiveWordEquiv CWSquareSupport depth).symm

@[simp] theorem positiveWordEquiv_dwz63WordEquiv (depth : ℕ)
    (word : Fin (depth + 1) → Fin 15) :
    positiveWordEquiv CWSquareSupport depth (dwz63WordEquiv depth word) =
      fun i ↦ dwz63CellEquiv (word i) := by
  simp only [dwz63WordEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- The multiplicity type of one transposed leg block is the corresponding pushforward of the
joint type of the supported-address word. -/
theorem multiplicity_supportWordAddress (depth : ℕ)
    (q : PositiveWord CWSquareSupport depth) (c : Leg) :
    WordType.multiplicity (positiveWordEquiv (Fin 5) depth
        (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ Fin 5)
          (support := cwSquareSupport) depth q c)) =
      WordType.mappedType (fun s : CWSquareSupport ↦ (s : CWSquareAddress) c)
        (WordType.multiplicity (positiveWordEquiv CWSquareSupport depth q)) := by
  rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
    (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport)]
  exact WordType.multiplicity_comp_eq_mappedType
    (fun s : CWSquareSupport ↦ (s : CWSquareAddress) c)
    (positiveWordEquiv CWSquareSupport depth q)

/-- On a transported section 6.3 word, the multiplicity type of one transposed leg block is the
corresponding section 6.3 coordinate marginal. -/
theorem multiplicity_supportWordAddress_dwz63WordEquiv (depth : ℕ)
    (word : Fin (depth + 1) → Fin 15) (c : Leg) :
    WordType.multiplicity (positiveWordEquiv (Fin 5) depth
        (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ Fin 5)
          (support := cwSquareSupport) depth (dwz63WordEquiv depth word) c)) =
      WordType.mappedType (dwz63LegIndex c) (WordType.multiplicity word) := by
  rw [multiplicity_supportWordAddress, positiveWordEquiv_dwz63WordEquiv]
  have hcomp : (fun i ↦ dwz63CellEquiv (word i)) =
      (dwz63CellEquiv : Fin 15 → CWSquareSupport) ∘ word := rfl
  rw [hcomp, WordType.multiplicity_comp_eq_mappedType, mappedType_legProj_cellEquiv]

/-! ## The ambient and marked families -/

/-- The three prescribed five-letter marginals, bundled by tensor leg. -/
def dwz63LegProfile (aX aY aZ : Fin 5 → ℕ) : Leg → Fin 5 → ℕ
  | .X => aX
  | .Y => aY
  | .Z => aZ

/-- **The section 6.3 ambient family, in the square-support word representation.**  These are the
words whose three transposed leg blocks carry the three prescribed five-letter types; unlike the
marked family it may contain several fifteen-cell joint types with those marginals, and that gap
is `[DuanWuZhou2022]`'s hash loss. -/
def dwz63AmbientWords (depth : ℕ) (aX aY aZ : Fin 5 → ℕ) :
    Finset (PositiveWord CWSquareSupport depth) := by
  classical
  exact Finset.univ.filter fun q ↦ ∀ c : Leg,
    WordType.multiplicity (positiveWordEquiv (Fin 5) depth
      (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ Fin 5)
        (support := cwSquareSupport) depth q c)) = dwz63LegProfile aX aY aZ c

theorem mem_dwz63AmbientWords {depth : ℕ} {aX aY aZ : Fin 5 → ℕ}
    {q : PositiveWord CWSquareSupport depth} :
    q ∈ dwz63AmbientWords depth aX aY aZ ↔ ∀ c : Leg,
      WordType.multiplicity (positiveWordEquiv (Fin 5) depth
        (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ Fin 5)
          (support := cwSquareSupport) depth q c)) = dwz63LegProfile aX aY aZ c := by
  classical
  simp [dwz63AmbientWords]

/-- **The section 6.3 marked family**: the exact fifteen-cell joint type, relabelled to the
coarsened square support. -/
def dwz63MarkedWords (depth : ℕ) (a : Fin 15 → ℕ) :
    Finset (PositiveWord CWSquareSupport depth) :=
  positiveTypeClass CWSquareSupport depth
    (WordType.mappedType (dwz63CellEquiv : Fin 15 → CWSquareSupport) a)

/-- **Identification (i)**: the transported three-marginal family `N_triple` is exactly the
family obtainable from the square partition by legwise block zeroing. -/
theorem mem_dwz63AmbientWords_dwz63WordEquiv (depth : ℕ) (aX aY aZ : Fin 5 → ℕ)
    (word : Fin (depth + 1) → Fin 15) :
    dwz63WordEquiv depth word ∈ dwz63AmbientWords depth aX aY aZ ↔
      word ∈ dwz63TripleSet (depth + 1) aX aY aZ := by
  rw [mem_dwz63AmbientWords, mem_dwz63TripleSet]
  simp only [multiplicity_supportWordAddress_dwz63WordEquiv]
  constructor
  · intro h
    exact ⟨h .X, h .Y, h .Z⟩
  · rintro ⟨hX, hY, hZ⟩ c
    cases c
    · exact hX
    · exact hY
    · exact hZ

/-- **Identification (ii)**: the transported exact fifteen-cell type class is the marked positive
type class. -/
theorem mem_dwz63MarkedWords_dwz63WordEquiv (depth : ℕ) (a : Fin 15 → ℕ)
    (word : Fin (depth + 1) → Fin 15) :
    dwz63WordEquiv depth word ∈ dwz63MarkedWords depth a ↔
      word ∈ WordType.typeClass (depth + 1) a := by
  rw [dwz63MarkedWords, mem_positiveTypeClass, WordType.mem_typeClass,
    positiveWordEquiv_dwz63WordEquiv]
  have hcomp : (fun i ↦ dwz63CellEquiv (word i)) =
      (dwz63CellEquiv : Fin 15 → CWSquareSupport) ∘ word := rfl
  rw [hcomp, WordType.multiplicity_comp_eq_mappedType]
  constructor
  · exact fun h ↦ mappedType_equiv_injective dwz63CellEquiv h
  · intro h
    rw [h]

/-- The ambient family has exactly `N_triple` elements. -/
theorem card_dwz63AmbientWords (depth : ℕ) (aX aY aZ : Fin 5 → ℕ) :
    (dwz63AmbientWords depth aX aY aZ).card =
      (dwz63TripleSet (depth + 1) aX aY aZ).card := by
  classical
  refine (Finset.card_bij (fun word _ ↦ dwz63WordEquiv depth word) ?_ ?_ ?_).symm
  · intro word hword
    exact (mem_dwz63AmbientWords_dwz63WordEquiv depth aX aY aZ word).2 hword
  · intro left _ right _ heq
    exact (dwz63WordEquiv depth).injective heq
  · intro q hq
    refine ⟨(dwz63WordEquiv depth).symm q, ?_, by simp⟩
    refine (mem_dwz63AmbientWords_dwz63WordEquiv depth aX aY aZ _).1 ?_
    simpa using hq

/-- The marked family has exactly `N_alpha` elements. -/
theorem card_dwz63MarkedWords (depth : ℕ) (a : Fin 15 → ℕ) :
    (dwz63MarkedWords depth a).card = (WordType.typeClass (depth + 1) a).card := by
  classical
  refine (Finset.card_bij (fun word _ ↦ dwz63WordEquiv depth word) ?_ ?_ ?_).symm
  · intro word hword
    exact (mem_dwz63MarkedWords_dwz63WordEquiv depth a word).2 hword
  · intro left _ right _ heq
    exact (dwz63WordEquiv depth).injective heq
  · intro q hq
    refine ⟨(dwz63WordEquiv depth).symm q, ?_, by simp⟩
    refine (mem_dwz63MarkedWords_dwz63WordEquiv depth a _).1 ?_
    simpa using hq

/-- **Identification (iii)**: a marked word has the three prescribed marginals, so the marked
family is contained in the ambient one.  The three hypotheses are exactly the marginal identities
of `M-DWZ9`. -/
theorem dwz63MarkedWords_subset_ambientWords (depth : ℕ) (a : Fin 15 → ℕ)
    (aX aY aZ : Fin 5 → ℕ)
    (hX : WordType.mappedType dwz63XIndex a = aX)
    (hY : WordType.mappedType dwz63YIndex a = aY)
    (hZ : WordType.mappedType dwz63ZIndex a = aZ) :
    dwz63MarkedWords depth a ⊆ dwz63AmbientWords depth aX aY aZ := by
  intro q hq
  have hjoint : WordType.multiplicity (positiveWordEquiv CWSquareSupport depth q) =
      WordType.mappedType (dwz63CellEquiv : Fin 15 → CWSquareSupport) a :=
    mem_positiveTypeClass.mp hq
  refine mem_dwz63AmbientWords.2 fun c ↦ ?_
  rw [multiplicity_supportWordAddress, hjoint, mappedType_legProj_cellEquiv]
  cases c
  · exact hX
  · exact hY
  · exact hZ

/-- The ambient family is invariant under a simultaneous permutation of all word positions.  This
is the stability hypothesis of
`PartitionHashEncoding.card_sourceWordLegFiber_eq_of_multiplicity_eq`. -/
theorem dwz63AmbientWords_reindex_mem_iff (depth : ℕ) (aX aY aZ : Fin 5 → ℕ)
    (e : Equiv.Perm (Fin (depth + 1)))
    (q : PositiveWord CWSquareSupport depth) :
    q ∈ dwz63AmbientWords depth aX aY aZ ↔
      PartitionHashEncoding.positiveWordReindex depth e q ∈
        dwz63AmbientWords depth aX aY aZ := by
  have key : ∀ (permutation : Equiv.Perm (Fin (depth + 1)))
      (source : PositiveWord CWSquareSupport depth),
      source ∈ dwz63AmbientWords depth aX aY aZ →
        PartitionHashEncoding.positiveWordReindex depth permutation source ∈
          dwz63AmbientWords depth aX aY aZ := by
    intro permutation source hsource
    refine mem_dwz63AmbientWords.2 fun c ↦ ?_
    have hreindex :=
      PartitionHashEncoding.positiveWordEquiv_supportWordAddress_reindex
        (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport)
        depth permutation source c
    rw [hreindex, WordType.multiplicity_reindex]
    exact mem_dwz63AmbientWords.1 hsource c
  refine ⟨key e q, fun hq ↦ ?_⟩
  have := key e.symm _ hq
  rwa [PartitionHashEncoding.positiveWordReindex_symm_apply] at this

/-! ## The section 6.3 instance -/

/-- At the section 6.3 data, marked containment is discharged by the committed marginal
identities: the fifteen-cell distribution has `X`- and `Y`-marginal `dwz63AlphaX` and `Z`-marginal
`dwz63AlphaZ`, all repeated proportionally. -/
theorem dwz63MarkedWords_subset_ambientWords_proportional (depth k : ℕ) :
    dwz63MarkedWords depth (WordType.proportionalCounts dwz63Alpha k) ⊆
      dwz63AmbientWords depth (WordType.proportionalCounts dwz63AlphaX k)
        (WordType.proportionalCounts dwz63AlphaX k)
        (WordType.proportionalCounts dwz63AlphaZ k) :=
  dwz63MarkedWords_subset_ambientWords depth _ _ _ _
    (mappedType_dwz63XIndex_proportionalCounts k)
    (mappedType_dwz63YIndex_proportionalCounts k)
    (mappedType_dwz63ZIndex_proportionalCounts k)

/-- The marked family at section 6.3's own repeated distribution is nonempty at the matching word
length, so the extraction it feeds is not vacuous. -/
theorem dwz63MarkedWords_nonempty {depth k : ℕ}
    (hlength : depth + 1 = WordType.profileMass dwz63Alpha * k) :
    (dwz63MarkedWords depth (WordType.proportionalCounts dwz63Alpha k)).Nonempty := by
  rw [← Finset.card_pos, card_dwz63MarkedWords]
  refine Finset.card_pos.mpr (WordType.typeClass_nonempty _ ?_)
  rw [hlength]
  exact proportionalCounts_dwz63Alpha_mem_types k

end

end AlgebraicComplexity.Examples
