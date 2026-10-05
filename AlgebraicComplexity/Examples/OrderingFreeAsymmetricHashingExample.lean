/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.OrderingFreeAsymmetricHashing
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-!
# A positive asymmetric-hashing instance with more used Z words

This finite client instantiates the asymmetric hashing estimate of [duan2023faster], §2.9,
`papers/sources/2210.10173/hashing.tex:7-13,32-65`, and the two degree costs of §6.3,
`component_value.tex:255-262`. It shows that the printed ordering is unnecessary: the complete
twelve-edge family has four used X words, four used Y words, and six used Z words.

The words are the length-four coordinate unit words, and the triples are
`(e_i,e_j,2-e_i-e_j)` with `i != j`, over `ZMod 29`. These are the full marginally induced
legal family and the good family. Each word is used: X/Y degrees are three and Z degrees two.
Each owner has one useful reference block, with compatibility exactly shared coarse Z.

The modulus inequality is `29 >= 8 * max(3,2)`. Literal applications of the generic expected
nonhole theorem and its seed-selection corollary give the positive constant `15/1682`.
All finite checks use the sixteen pair addresses or four word coordinates; no seed family is
enumerated. Two fixed seeds additionally show an intact useful block and two X/Y-isolated
owners whose shared Z removes both useful blocks. This is a finite hashing client, with no
asymptotic or matrix exponent conclusion.
-/

namespace AlgebraicComplexity.OrderingFreeAsymmetricHashingExample

open ProgressionHash ProgressionHash.LegalTriple
open scoped BigOperators

private abbrev Triple := LegalTriple (ZMod 29) (Fin 4) 2
private abbrev Address := Fin 4 × Fin 4

private instance prime29 : Fact (Nat.Prime 29) := ⟨by decide⟩
private instance two_ne_zero : NeZero (2 : ZMod 29) := ⟨by decide⟩
private noncomputable instance tripleDecidableEq : DecidableEq Triple := Classical.decEq _

/-- The coordinate word with one at position `i` and zero at the other three positions. -/
def unitWord (i : Fin 4) : Fin 4 → ZMod 29 := fun k ↦ if k = i then 1 else 0

/-- The tight triple determined by an ordered pair of unit words; the ambient family below
uses precisely the pairs with different entries. -/
def edge (a : Fin 4 × Fin 4) : LegalTriple (ZMod 29) (Fin 4) 2 where
  xIndex := unitWord a.1
  yIndex := unitWord a.2
  zIndex := fun k ↦ 2 - unitWord a.1 k - unitWord a.2 k
  legal k := by ring

private theorem unitWord_injective : Function.Injective unitWord := by
  intro i j h
  by_contra hne
  have hi := congrFun h i
  simp [unitWord, hne] at hi

private theorem edge_injective : Function.Injective edge := by
  intro a b h
  exact Prod.ext (unitWord_injective (congrArg LegalTriple.xIndex h))
    (unitWord_injective (congrArg LegalTriple.yIndex h))

private def addresses : Finset Address := Finset.univ.filter fun a ↦ a.1 ≠ a.2

/-- The complete twelve-edge family, used both as the ambient family and as its good subfamily.
There are no added vertices or omitted marginally induced legal triples. -/
noncomputable def ambient : Finset (LegalTriple (ZMod 29) (Fin 4) 2) := by
  classical
  exact addresses.image edge

/-- The single progression-free bucket at zero. -/
def buckets : Finset (ZMod 29) := {0}

/-- Every owner has one reference block, and that block is useful. -/
def useful (_owner : LegalTriple (ZMod 29) (Fin 4) 2) : Finset Unit := Finset.univ

/-- A competitor is compatible with the unique fine block exactly when it shares the owner's
actual coarse Z word. -/
def compatibility (owner : LegalTriple (ZMod 29) (Fin 4) 2) (_fine : Unit)
    (competitor : LegalTriple (ZMod 29) (Fin 4) 2) : Prop :=
  competitor.zIndex = owner.zIndex

/-- The ambient and good families have twelve distinct triples. -/
theorem card_ambient : ambient.card = 12 := by
  classical
  rw [ambient, Finset.card_image_of_injective _ edge_injective]
  decide

private theorem addressXCount : (addresses.image fun a ↦ (edge a).xIndex).card = 4 := by
  decide

private theorem addressYCount : (addresses.image fun a ↦ (edge a).yIndex).card = 4 := by
  decide

private theorem addressZCount : (addresses.image fun a ↦ (edge a).zIndex).card = 6 := by
  decide

/-- Cardinalities count precisely the words occurring in a triple: four X words, four Y words,
and six Z words. In particular the used Z count is strictly larger than the used X count. -/
theorem usedVertexCounts :
    (ambient.image LegalTriple.xIndex).card = 4 ∧
    (ambient.image LegalTriple.yIndex).card = 4 ∧
    (ambient.image LegalTriple.zIndex).card = 6 := by
  classical
  simp only [ambient, Finset.image_image]
  exact ⟨addressXCount, addressYCount, addressZCount⟩

private theorem offDiagonal_of_z_eq :
    ∀ a b : Address, b.1 ≠ b.2 → (edge a).zIndex = (edge b).zIndex → a.1 ≠ a.2 := by
  decide

/-- Every legal triple using the active X, Y and Z word sets is already in `ambient`.

Proof sketch: read the X/Y positions from their image witnesses. Their unit words determine the
whole legal triple. Equality to an active Z word forces the positions to differ. -/
theorem fullAmbient (triple : LegalTriple (ZMod 29) (Fin 4) 2) :
    triple ∈ ambient ↔
      triple.xIndex ∈ ambient.image LegalTriple.xIndex ∧
      triple.yIndex ∈ ambient.image LegalTriple.yIndex ∧
      triple.zIndex ∈ ambient.image LegalTriple.zIndex := by
  classical
  constructor
  · intro h
    exact ⟨Finset.mem_image.mpr ⟨triple, h, rfl⟩,
      Finset.mem_image.mpr ⟨triple, h, rfl⟩,
      Finset.mem_image.mpr ⟨triple, h, rfl⟩⟩
  · rintro ⟨hx, hy, hz⟩
    simp only [ambient, Finset.image_image, Finset.mem_image] at hx hy hz
    obtain ⟨a, _ha, hx⟩ := hx
    obtain ⟨b, _hb, hy⟩ := hy
    obtain ⟨c, hc, hz⟩ := hz
    have ht : triple = edge (a.1, b.2) :=
      eq_of_xIndex_eq_yIndex_eq hx.symm hy.symm
    subst triple
    exact Finset.mem_image.mpr ⟨(a.1, b.2),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        offDiagonal_of_z_eq _ c (Finset.mem_filter.mp hc).2 hz.symm⟩, rfl⟩

private def addressFiber (a : Address) (leg : Tensor.Leg) : Finset Address :=
  addresses.filter fun b ↦ (edge b).legIndex leg = (edge a).legIndex leg

private theorem addressXDegree : ∀ a : Address, a.1 ≠ a.2 →
    (addressFiber a .X).card = 3 := by
  decide

private theorem addressYDegree : ∀ a : Address, a.1 ≠ a.2 →
    (addressFiber a .Y).card = 3 := by
  decide

private theorem addressZDegree : ∀ a : Address, a.1 ≠ a.2 →
    (addressFiber a .Z).card = 2 := by
  decide

/-- Membership, rather than reduction of classical finite sets, identifies the address fiber. -/
private theorem legFiber_eq_image (a : Address) (leg : Tensor.Leg) :
    legFiber ambient (edge a) leg = (addressFiber a leg).image edge := by
  classical
  ext triple
  simp only [mem_legFiber, ambient, Finset.mem_image, addressFiber, Finset.mem_filter]
  constructor
  · rintro ⟨⟨b, hb, rfl⟩, hleg⟩
    exact ⟨b, ⟨hb, hleg⟩, rfl⟩
  · rintro ⟨b, ⟨hb, hleg⟩, rfl⟩
    exact ⟨⟨b, hb, rfl⟩, hleg⟩

/-- Every used X/Y word has full ambient degree three and every used Z word has degree two.
The same equations give good degrees because the good family equals the ambient family. -/
theorem legFiber_card (owner : LegalTriple (ZMod 29) (Fin 4) 2) (howner : owner ∈ ambient) :
    (legFiber ambient owner .X).card = 3 ∧
    (legFiber ambient owner .Y).card = 3 ∧
    (legFiber ambient owner .Z).card = 2 := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp howner
  have hne := (Finset.mem_filter.mp ha).2
  constructor
  · rw [legFiber_eq_image, Finset.card_image_of_injective _ edge_injective]
    exact addressXDegree a hne
  constructor
  · rw [legFiber_eq_image, Finset.card_image_of_injective _ edge_injective]
    exact addressYDegree a hne
  · rw [legFiber_eq_image, Finset.card_image_of_injective _ edge_injective]
    exact addressZDegree a hne

private def addressFineCompetitors (a : Address) : Finset Address :=
  (addresses.erase a).filter fun b ↦ (edge b).zIndex = (edge a).zIndex

private theorem addressCompatibleDegree : ∀ a : Address, a.1 ≠ a.2 →
    (addressFineCompetitors a).card = 1 := by
  decide

/-- The one other compatible good triple is the reversed ordered pair. Thus the shared-Z cost
is real, and the paper's full Z degree budget `c = 2` bounds it. -/
theorem fineCompetitors_card (owner : LegalTriple (ZMod 29) (Fin 4) 2)
    (howner : owner ∈ ambient) (fine : Unit) :
    (fineCompetitors ambient compatibility owner fine).card = 1 := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp howner
  have hfine : fineCompetitors ambient compatibility (edge a) fine =
      (addressFineCompetitors a).image edge := by
    ext triple
    simp only [mem_fineCompetitors, compatibility, ambient, Finset.mem_image,
      addressFineCompetitors, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hne, ⟨b, hb, rfl⟩⟩, hz⟩
      exact ⟨b, ⟨⟨fun h ↦ hne (congrArg edge h), hb⟩, hz⟩, rfl⟩
    · rintro ⟨b, ⟨⟨hne, hb⟩, hz⟩, rfl⟩
      exact ⟨⟨fun h ↦ hne (edge_injective h), ⟨b, hb, rfl⟩⟩, hz⟩
  rw [hfine, Finset.card_image_of_injective _ edge_injective]
  exact addressCompatibleDegree a (Finset.mem_filter.mp ha).2

/-- The ordering-free expected useful nonhole mass is at least the strictly positive rational
`15/1682`, despite the genuinely used counts `N_Z = 6 > 4 = N_X = N_Y`.

Proof sketch: literally instantiate the shared expected-mass theorem with `d = 3`, `c = 2`,
`theta = 1`, the full twelve-edge family, and the one-element useful references. -/
theorem expected_nonhole_positive :
    0 < (15 / 1682 : ℚ) ∧
      (15 / 1682 : ℚ) ≤
        (∑ seed : Seed (ZMod 29) (Fin 4),
          seedMarkedXYNonholeFraction (fun _ : Triple ↦ Unit)
            ambient ambient buckets useful compatibility seed) /
              Fintype.card (Seed (ZMod 29) (Fin 4)) := by
  refine ⟨by norm_num, ?_⟩
  have h := five_eighths_le_expected_seedMarkedXYNonholeFraction
    (fun _ : Triple ↦ Unit) ambient ambient buckets useful compatibility 3 2 1
    (fun owner howner ↦ (legFiber_card owner howner).1.le)
    (fun owner howner ↦ (legFiber_card owner howner).2.1.le)
    (by norm_num [ZMod.card])
    (by intro owner howner; simp)
    (by intro owner howner; simp [useful])
    (by intro owner howner fine hfine competitor hcompetitor hne hcompat; exact hcompat)
    (by
      intro owner howner fine hfine
      change (fineCompetitors ambient compatibility owner fine).card ≤ 2
      rw [fineCompetitors_card owner howner fine]
      decide)
  norm_num [buckets, card_ambient, ZMod.card] at h
  exact h

/-- One seed has useful nonhole mass at least `15/1682`; its selected owners survive filtering
of the full ambient family and use distinct X words and distinct Y words.

Proof sketch: instantiate the generic seed-selection corollary with the same concrete data.
The theorem retains the selected family's semantics as well as the positive quantitative bound. -/
theorem exists_positive_seed : ∃ seed : Seed (ZMod 29) (Fin 4),
    (15 / 1682 : ℚ) ≤ seedMarkedXYNonholeFraction (fun _ : Triple ↦ Unit)
      ambient ambient buckets useful compatibility seed ∧
    markedXYIsolatedTargets ambient ambient buckets seed ⊆
      filteredTargets ambient buckets seed ∧
    Set.InjOn (fun triple : Triple ↦ triple.xIndex)
      (markedXYIsolatedTargets ambient ambient buckets seed : Set _) ∧
    Set.InjOn (fun triple : Triple ↦ triple.yIndex)
      (markedXYIsolatedTargets ambient ambient buckets seed : Set _) := by
  have h := exists_seed_markedXYNonholeFraction
    (fun _ : Triple ↦ Unit) ambient ambient (fun _ h ↦ h) buckets
    (by simp [buckets])
    useful compatibility 3 2 1
    (fun owner howner ↦ (legFiber_card owner howner).1.le)
    (fun owner howner ↦ (legFiber_card owner howner).2.1.le)
    (by norm_num [ZMod.card])
    (by intro owner howner; simp)
    (by intro owner howner; simp [useful])
    (by intro owner howner fine hfine competitor hcompetitor hne hcompat; exact hcompat)
    (by
      intro owner howner fine hfine
      change (fineCompetitors ambient compatibility owner fine).card ≤ 2
      rw [fineCompetitors_card owner howner fine]
      decide)
  norm_num [buckets, card_ambient, ZMod.card] at h
  exact h

/-- A fixed seed whose isolated owner at address `(0,1)` retains its useful fine block. -/
def positiveSeed : Seed (ZMod 29) (Fin 4) := ⟨0, 28, ![0, 1, 2, 2]⟩

/-- A fixed seed retaining both reversed owners `(0,1)` and `(1,0)` before shared-Z cleanup.
Both owners lose their useful fine block to the other owner. -/
def damageSeed : Seed (ZMod 29) (Fin 4) := ⟨0, 0, ![0, 0, 1, 1]⟩

private theorem xHash_unitWord (seed : Seed (ZMod 29) (Fin 4)) (i : Fin 4) :
    seed.xHash (unitWord i) = seed.offset + seed.weights i := by
  simp [Seed.xHash, hashX, linear, unitWord, mul_ite]

private theorem yHash_unitWord (seed : Seed (ZMod 29) (Fin 4)) (i : Fin 4) :
    seed.yHash (unitWord i) = seed.offset + seed.shift + seed.weights i := by
  simp [Seed.yHash, hashY, linear, unitWord, mul_ite]

/-- Transfer the concrete alternative-hash checks to the shared X/Y isolation interface. -/
private theorem isolated_of_address_checks (seed : Seed (ZMod 29) (Fin 4))
    (a : Address) (ha : a ∈ addresses)
    (hcommon : Seed.InCommonBucket (edge a).xIndex (edge a).yIndex 0 seed)
    (hchecks : ∀ b ∈ addresses, b ≠ a →
      (b.1 = a.1 → seed.offset + seed.shift + seed.weights b.2 ≠ 0) ∧
      (b.2 = a.2 → seed.offset + seed.weights b.1 ≠ 0)) :
    edge a ∈ markedXYIsolatedTargets ambient ambient buckets seed := by
  classical
  letI : DecidableEq (ZMod 29) := Classical.decEq _
  unfold markedXYIsolatedTargets Seed.isolatedTargets
  refine Finset.mem_image.mpr ⟨(edge a, 0), ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩,
    by simp [buckets]⟩, hcommon, ?_⟩
  intro alternative halternative
  obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp halternative
  obtain ⟨herase, hshare⟩ := Finset.mem_filter.mp hother
  obtain ⟨hne, hother⟩ := Finset.mem_erase.mp herase
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hother
  have hba : b ≠ a := fun h ↦ hne (congrArg edge h)
  unfold collisionProxy
  split_ifs with hx
  · change seed.yHash (unitWord b.2) ≠ 0
    rw [yHash_unitWord]
    exact (hchecks b hb hba).1 (unitWord_injective hx)
  · rw [Seed.yHash_transportXAlternative_eq_xHash seed _ _ _ 0 hcommon]
    change seed.xHash (unitWord b.1) ≠ 0
    rw [xHash_unitWord]
    rcases hshare with hX | hY
    · exact False.elim (hx hX.symm)
    · exact (hchecks b hb hba).2 (unitWord_injective hY.symm)

private theorem positive_address_checks : ∀ b ∈ addresses, b ≠ (0, 1) →
    (b.1 = 0 → positiveSeed.offset + positiveSeed.shift + positiveSeed.weights b.2 ≠ 0) ∧
    (b.2 = 1 → positiveSeed.offset + positiveSeed.weights b.1 ≠ 0) := by
  decide

private theorem positive_shared_competitor_misses : ∀ b ∈ addresses, b ≠ (0, 1) →
    (edge b).zIndex = (edge (0, 1)).zIndex →
      positiveSeed.offset + positiveSeed.weights b.1 ≠ 0 := by
  decide

/-- The explicit positive seed retains owner `(0,1)` after full ambient X/Y isolation, and
its one useful reference block is not a hole. No existential seed enumeration is used. -/
theorem positiveSeed_nonhole :
    edge (0, 1) ∈ markedXYIsolatedTargets ambient ambient buckets positiveSeed ∧
    seedSharedHoles ambient compatibility positiveSeed (edge (0, 1)) 0 = ∅ := by
  classical
  constructor
  · apply isolated_of_address_checks positiveSeed (0, 1) (by decide)
    · change positiveSeed.xHash (unitWord 0) = 0 ∧ positiveSeed.yHash (unitWord 1) = 0
      rw [xHash_unitWord, yHash_unitWord]
      decide
    · exact positive_address_checks
  · apply Finset.eq_empty_of_forall_notMem
    intro fine hfine
    obtain ⟨_, other, hother, hcommon⟩ := Finset.mem_filter.mp hfine
    obtain ⟨⟨hne, hother⟩, hcompat⟩ := mem_fineCompetitors.mp hother
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hother
    have hbne : b ≠ (0, 1) := fun h ↦ hne (congrArg edge h)
    have hmiss := positive_shared_competitor_misses b hb hbne hcompat
    exact hmiss ((xHash_unitWord positiveSeed b.1).symm.trans hcommon.1)

private theorem damage_address_checks : ∀ a : Address, a = (0, 1) ∨ a = (1, 0) →
    ∀ b ∈ addresses, b ≠ a →
      (b.1 = a.1 → damageSeed.offset + damageSeed.shift + damageSeed.weights b.2 ≠ 0) ∧
      (b.2 = a.2 → damageSeed.offset + damageSeed.weights b.1 ≠ 0) := by
  decide

private theorem damage_address_common : ∀ a : Address, a = (0, 1) ∨ a = (1, 0) →
    damageSeed.offset + damageSeed.weights a.1 = 0 ∧
      damageSeed.offset + damageSeed.shift + damageSeed.weights a.2 = 0 := by
  decide

private theorem damage_reverse_facts : ∀ a : Address, a = (0, 1) ∨ a = (1, 0) →
    (a.2, a.1) ∈ addresses ∧ (a.2, a.1) ≠ a ∧
    (edge (a.2, a.1)).zIndex = (edge a).zIndex ∧
    ((a.2, a.1) = (0, 1) ∨ (a.2, a.1) = (1, 0)) := by
  decide

private theorem damage_common (a : Address) (ha : a = (0, 1) ∨ a = (1, 0)) :
    Seed.InCommonBucket (edge a).xIndex (edge a).yIndex 0 damageSeed := by
  change damageSeed.xHash (unitWord a.1) = 0 ∧ damageSeed.yHash (unitWord a.2) = 0
  rw [xHash_unitWord, yHash_unitWord]
  exact damage_address_common a ha

private theorem damage_all_holes (a : Address) (ha : a = (0, 1) ∨ a = (1, 0)) :
    seedSharedHoles ambient compatibility damageSeed (edge a) 0 = useful (edge a) := by
  classical
  ext fine
  simp only [useful, Finset.mem_univ, iff_true]
  apply Finset.mem_filter.mpr
  have hreverse := damage_reverse_facts a ha
  refine ⟨Finset.mem_univ _, edge (a.2, a.1), ?_, ?_⟩
  · apply mem_fineCompetitors.mpr
    exact ⟨⟨fun h ↦ hreverse.2.1 (edge_injective h),
      Finset.mem_image.mpr ⟨(a.2, a.1), hreverse.1, rfl⟩⟩, hreverse.2.2.1⟩
  · exact (Seed.inCommonTriple_iff_commonBucket damageSeed _ _ _ 2 0
      (edge (a.2, a.1)).legal).mpr (damage_common _ hreverse.2.2.2)

/-- The damage seed retains two distinct X/Y-isolated owners sharing Z, and both lose their
entire useful reference to the other owner. Thus X/Y isolation does not make shared-Z cleanup
vacuous in this very instance.

Proof sketch: check each owner's four actual X/Y competitors on the sixteen address space;
the reversed pair survives in the same zero bucket and witnesses the unique useful block's hole. -/
theorem damageSeed_sharedZ :
    edge (0, 1) ≠ edge (1, 0) ∧
    (edge (0, 1)).zIndex = (edge (1, 0)).zIndex ∧
    edge (0, 1) ∈ markedXYIsolatedTargets ambient ambient buckets damageSeed ∧
    edge (1, 0) ∈ markedXYIsolatedTargets ambient ambient buckets damageSeed ∧
    seedSharedHoles ambient compatibility damageSeed (edge (0, 1)) 0 = useful (edge (0, 1)) ∧
    seedSharedHoles ambient compatibility damageSeed (edge (1, 0)) 0 = useful (edge (1, 0)) := by
  refine ⟨?_, ?_, ?_, ?_, damage_all_holes _ (Or.inl rfl),
    damage_all_holes _ (Or.inr rfl)⟩
  · intro h
    have := edge_injective h
    have : (0 : Fin 4) = 1 := congrArg Prod.fst this
    exact (by decide : (0 : Fin 4) ≠ 1) this
  · funext k
    simp only [edge]
    ring
  · exact isolated_of_address_checks damageSeed (0, 1) (by decide)
      (damage_common _ (Or.inl rfl)) (damage_address_checks _ (Or.inl rfl))
  · exact isolated_of_address_checks damageSeed (1, 0) (by decide)
      (damage_common _ (Or.inr rfl)) (damage_address_checks _ (Or.inr rfl))

end AlgebraicComplexity.OrderingFreeAsymmetricHashingExample
