/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourShapeDefs
import Mathlib.Tactic.Order

/-!
# Finite shape geometry for recursive level-four certificates

This module proves the support and indexing facts about the executable definitions in
`LevelFourShapeDefs`.  Probability vectors and dyadic tables are deliberately absent.
-/

namespace AlgebraicComplexity.LevelFourReconstruction

namespace Shape

theorem complement_add_of_le {u s : Shape} (h : u ≤ s) :
    u.x + (s.complement u).x = s.x ∧
      u.y + (s.complement u).y = s.y ∧
      u.z + (s.complement u).z = s.z := by
  exact ⟨Nat.add_sub_of_le h.1, Nat.add_sub_of_le h.2.1, Nat.add_sub_of_le h.2.2⟩

theorem complement_total_of_le {u s : Shape} (h : u ≤ s) :
    (s.complement u).total = s.total - u.total := by
  rcases h with ⟨hx, hy, hz⟩
  simp only [total, complement]
  omega

end Shape

/-- There are exactly twenty-one positive triples summing to eight. -/
theorem positiveShapes_eight_length : (positiveShapes 8).length = 21 := by
  decide

/-- Explicit order of the positive total-eight shapes used by the certificate index. -/
theorem positiveShapes_eight_eq :
    positiveShapes 8 =
      [⟨1, 1, 6⟩, ⟨1, 2, 5⟩, ⟨1, 3, 4⟩, ⟨1, 4, 3⟩, ⟨1, 5, 2⟩, ⟨1, 6, 1⟩,
        ⟨2, 1, 5⟩, ⟨2, 2, 4⟩, ⟨2, 3, 3⟩, ⟨2, 4, 2⟩, ⟨2, 5, 1⟩,
        ⟨3, 1, 4⟩, ⟨3, 2, 3⟩, ⟨3, 3, 2⟩, ⟨3, 4, 1⟩,
        ⟨4, 1, 3⟩, ⟨4, 2, 2⟩, ⟨4, 3, 1⟩,
        ⟨5, 1, 2⟩, ⟨5, 2, 1⟩, ⟨6, 1, 1⟩] := by
  decide

/-- Every shape reconstructed by `shapes` has the requested coordinate sum. -/
theorem mem_shapes_total {n : ℕ} {s : Shape} (h : s ∈ shapes n) : s.total = n := by
  simp only [shapes, List.mem_flatMap, List.mem_range, List.mem_map] at h
  rcases h with ⟨x, hx, y, hy, rfl⟩
  simp only [Shape.total]
  omega

/-- The explicit enumeration contains every triple with the prescribed coordinate sum. -/
theorem mem_shapes_iff_total {n : ℕ} {s : Shape} : s ∈ shapes n ↔ s.total = n := by
  constructor
  · exact mem_shapes_total
  · intro htotal
    simp only [shapes, List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨s.x, ?_, s.y, ?_, ?_⟩
    · simp only [Shape.total] at htotal
      omega
    · simp only [Shape.total] at htotal
      omega
    · congr
      simp only [Shape.total] at htotal
      omega

/-- Membership in `positiveShapes` gives positivity and the prescribed total. -/
theorem mem_positiveShapes {n : ℕ} {s : Shape} (h : s ∈ positiveShapes n) :
    s.IsPositive ∧ s.total = n := by
  simp only [positiveShapes, List.mem_filter] at h
  exact ⟨of_decide_eq_true h.2, mem_shapes_total h.1⟩

/-- A reconstructed level-three split has total four and is contained in its parent. -/
theorem mem_levelThreeSplits {parent child : Shape} (h : child ∈ levelThreeSplits parent) :
    child.total = 4 ∧ child ≤ parent := by
  simp only [levelThreeSplits, List.mem_filter] at h
  exact ⟨mem_shapes_total h.1, of_decide_eq_true h.2⟩

/-- Exact support characterization for a level-three split. -/
theorem mem_levelThreeSplits_iff {parent child : Shape} :
    child ∈ levelThreeSplits parent ↔ child.total = 4 ∧ child ≤ parent := by
  simp only [levelThreeSplits, List.mem_filter, decide_eq_true_eq, mem_shapes_iff_total]

/-- At a level-three parent of total eight, the complementary child also has total four. -/
theorem complement_total_four_of_mem_levelThreeSplits
    {parent child : Shape} (hparent : parent.total = 8)
    (hchild : child ∈ levelThreeSplits parent) :
    (parent.complement child).total = 4 := by
  rw [Shape.complement_total_of_le (mem_levelThreeSplits hchild).2,
    hparent, (mem_levelThreeSplits hchild).1]

/-- Ten slots suffice for every split list of a positive level-three parent. -/
theorem levelThreeSplits_length_le_ten
    {parent : Shape} (h : parent ∈ positiveShapes 8) :
    (levelThreeSplits parent).length ≤ 10 := by
  have hcases :
      parent = ⟨1, 1, 6⟩ ∨ parent = ⟨1, 2, 5⟩ ∨ parent = ⟨1, 3, 4⟩ ∨
      parent = ⟨1, 4, 3⟩ ∨ parent = ⟨1, 5, 2⟩ ∨ parent = ⟨1, 6, 1⟩ ∨
      parent = ⟨2, 1, 5⟩ ∨ parent = ⟨2, 2, 4⟩ ∨ parent = ⟨2, 3, 3⟩ ∨
      parent = ⟨2, 4, 2⟩ ∨ parent = ⟨2, 5, 1⟩ ∨ parent = ⟨3, 1, 4⟩ ∨
      parent = ⟨3, 2, 3⟩ ∨ parent = ⟨3, 3, 2⟩ ∨ parent = ⟨3, 4, 1⟩ ∨
      parent = ⟨4, 1, 3⟩ ∨ parent = ⟨4, 2, 2⟩ ∨ parent = ⟨4, 3, 1⟩ ∨
      parent = ⟨5, 1, 2⟩ ∨ parent = ⟨5, 2, 1⟩ ∨ parent = ⟨6, 1, 1⟩ := by
    simpa only [positiveShapes_eight_eq, List.mem_cons, List.not_mem_nil, or_false] using h
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

namespace PositiveLevelThreeData

/-- Every node index denotes one of the twenty-one positive shapes of total eight. -/
theorem nodeShape_mem_positiveShapes (node : Fin nodeCount) :
    nodeShape node ∈ positiveShapes 8 := by
  have hi : node.val / regionCount < (positiveShapes 8).length := by
    rw [positiveShapes_eight_length]
    have hn := node.isLt
    simp only [nodeCount, regionCount] at hn ⊢
    omega
  unfold nodeShape
  rw [List.getElem?_eq_getElem hi]
  exact List.getElem_mem (l := positiveShapes 8) hi

/-- Every node shape is positive and has coordinate sum eight. -/
theorem nodeShape_geometry (node : Fin nodeCount) :
    (nodeShape node).IsPositive ∧ (nodeShape node).total = 8 :=
  mem_positiveShapes (nodeShape_mem_positiveShapes node)

/-- A valid padded slot is exactly an element of the reconstructed split list. -/
theorem splitShape_mem_levelThreeSplits
    (node : Fin nodeCount) (slot : Fin splitSlotCount)
    (hslot : splitSlotValid node slot) :
    splitShape node slot ∈ levelThreeSplits (nodeShape node) := by
  unfold splitSlotValid at hslot
  unfold splitShape
  rw [List.getElem?_eq_getElem hslot]
  exact List.getElem_mem (l := levelThreeSplits (nodeShape node)) hslot

/-- Each valid slot reconstructs two complementary level-two shapes of total four. -/
theorem splitShape_geometry
    (node : Fin nodeCount) (slot : Fin splitSlotCount)
    (hslot : splitSlotValid node slot) :
    (splitShape node slot).total = 4 ∧
      splitShape node slot ≤ nodeShape node ∧
      ((nodeShape node).complement (splitShape node slot)).total = 4 := by
  have hmem := splitShape_mem_levelThreeSplits node slot hslot
  exact ⟨(mem_levelThreeSplits hmem).1, (mem_levelThreeSplits hmem).2,
    complement_total_four_of_mem_levelThreeSplits (nodeShape_geometry node).2 hmem⟩

end PositiveLevelThreeData

end AlgebraicComplexity.LevelFourReconstruction
