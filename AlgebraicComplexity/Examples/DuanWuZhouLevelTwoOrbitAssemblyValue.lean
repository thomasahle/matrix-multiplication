/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitAssembly
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTargetWordCount
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoIntegrationMarkedFamily
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAlphaAddressCells

/-!
# The value of a target-typical six-orientation constituent

Layer 4 (`AlgebraicComplexity/Examples/`).  The arithmetic left open by
`Examples/DuanWuZhouLevelTwoOrbitAssembly.lean`: the symmetrized multiplicities of a
target-typical six-orientation word, and the mass they carry on the `(1,1,2)` orbit.

The evaluations of `dwz63AlphaAddress` at the three exceptional coarse addresses that this module
used to carry now live in `Examples/DuanWuZhouLevelTwoAlphaAddressCells.lean`, so that the live
plain-partition client can use them without importing the six-orientation value chain; they are
imported back here.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173 (`[DuanWuZhou2022]`), `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

/-! ## Multiplicities of the six oriented sub-words at a target-typical word -/

section Typical

variable {K : Type u} [CommRing K] {n t : ℕ}
variable {q : PositiveWord ((dwz63SymSixPartition K).support) n}

theorem dwz63_mult_symSixWord0 (htyp : Dwz63TargetTypical K n t q)
    (s : (cwSquarePartitionedTensor K dwz63Q).support) :
    WordType.multiplicity (positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord0 n q)) s = dwz63AlphaAddress s.1 * t := by
  rw [dwz63_multiplicity_symSixWord0 n q s, congrFun (htyp 0) s.1]
  rfl

theorem dwz63_mult_symSixWord1 (htyp : Dwz63TargetTypical K n t q)
    (s : ((cwSquarePartitionedTensor K dwz63Q).permute cycle).support) :
    WordType.multiplicity (positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord1 n q)) s = dwz63AlphaAddress s.1 * t := by
  rw [dwz63_multiplicity_symSixWord1 n q s, congrFun (htyp 1) s.1]
  rfl

theorem dwz63_mult_symSixWord2 (htyp : Dwz63TargetTypical K n t q)
    (s : ((cwSquarePartitionedTensor K dwz63Q).permute cycle.symm).support) :
    WordType.multiplicity (positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord2 n q)) s = dwz63AlphaAddress s.1 * t := by
  rw [dwz63_multiplicity_symSixWord2 n q s, congrFun (htyp 2) s.1]
  rfl

theorem dwz63_mult_symSixWord3 (htyp : Dwz63TargetTypical K n t q)
    (s : ((cwSquarePartitionedTensor K dwz63Q).permute swapXY).support) :
    WordType.multiplicity (positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord3 n q)) s = dwz63AlphaAddress s.1 * t := by
  rw [dwz63_multiplicity_symSixWord3 n q s, congrFun (htyp 3) s.1]
  rfl

theorem dwz63_mult_symSixWord4 (htyp : Dwz63TargetTypical K n t q)
    (s : ((cwSquarePartitionedTensor K dwz63Q).permute (cycle.trans swapXY)).support) :
    WordType.multiplicity (positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord4 n q)) s = dwz63AlphaAddress s.1 * t := by
  rw [dwz63_multiplicity_symSixWord4 n q s, congrFun (htyp 4) s.1]
  rfl

theorem dwz63_mult_symSixWord5 (htyp : Dwz63TargetTypical K n t q)
    (s : ((cwSquarePartitionedTensor K dwz63Q).permute (cycle.symm.trans swapXY)).support) :
    WordType.multiplicity (positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord5 n q)) s = dwz63AlphaAddress s.1 * t := by
  rw [dwz63_multiplicity_symSixWord5 n q s, congrFun (htyp 5) s.1]
  rfl

end Typical

/-! ## The `C₃`-coset Latin square

`hasTauWeight_symSixHalf` consumes, per orientation of a coset, three constant orbit blocks in the
tag order `π`, `cycle · π`, `cycle⁻¹ · π`.  Which of the three orbit *cells* lands in which tag
slot depends on the orientation, and the dependence is a Latin square that is uniform in the coset
representative `π`: `dwz63RawTag e s = (dwz63OrbitRotation s).trans e`, and the three rotations are
`1`, `cycle⁻¹`, `cycle` at `(1,1,2)`, `(1,2,1)`, `(2,1,1)`.
-/

section Latin

/-- The three orientations of the `C₃`-coset of `π`, in the association
`symSixPartition` uses. -/
def dwz63HalfOrientation (π : Orientation) : Fin 3 → Orientation :=
  ![π, cycle.trans π, cycle.symm.trans π]

/-- **The Latin square**: `dwz63HalfCell i k` is the orbit cell that the `i`-th orientation of a
coset must contribute to the `k`-th tag slot. -/
def dwz63HalfCell : Fin 3 → Fin 3 → CWSquareAddress :=
  ![![cwSquare112, cwSquare211, cwSquare121],
    ![cwSquare121, cwSquare112, cwSquare211],
    ![cwSquare211, cwSquare121, cwSquare112]]

-- The two `C₃` relations this section needs, `cycle.trans cycle = cycle.symm` and
-- `cycle.symm.trans cycle.symm = cycle`, are discharged inline by `decide` at each use.  The
-- first of them is also `AlgebraicComplexity.Tensor.cycle_trans_cycle`
-- (`MatrixMultiplication/SixSymmetrizedValue.lean`); it is not named again here, to keep
-- `cycle_trans_cycle` unambiguous under `open Tensor`.

/-- Every `dwz63HalfCell` entry is an orbit cell. -/
theorem dwz63HalfCell_mem_orbit (i k : Fin 3) : dwz63HalfCell i k ∈ cwSquare112Orbit := by
  revert i k; decide

/-- Every `dwz63HalfCell` entry is a supported coarse address. -/
theorem dwz63HalfCell_mem_support (i k : Fin 3) : dwz63HalfCell i k ∈ cwSquareSupport := by
  revert i k; decide

/-- The three cells an orientation contributes are pairwise distinct: the Latin square has no
repeated entry in a row. -/
theorem dwz63HalfCell_injective (i : Fin 3) {k l : Fin 3} (h : k ≠ l) :
    dwz63HalfCell i k ≠ dwz63HalfCell i l := by
  revert i k l; decide

/-- Group identities used by the Latin square, in the form the case split consumes. -/
theorem dwz63_trans_assoc_eq {π g h j : Orientation} (hj : g.trans h = j) :
    g.trans (h.trans π) = j.trans π := by
  rw [← Equiv.trans_assoc, hj]

theorem dwz63_trans_assoc_one {π g h : Orientation} (hj : g.trans h = 1) :
    g.trans (h.trans π) = π := by
  rw [← Equiv.trans_assoc, hj]
  exact Equiv.refl_trans π

theorem dwz63_trans_one {π g : Orientation} (hg : g = 1) : g.trans π = π := by
  rw [hg]
  exact Equiv.refl_trans π

set_option maxRecDepth 4000 in
set_option linter.unusedSimpArgs false in
/-- **The tag of the Latin-square entry is the tag slot.**

The `i`-th orientation of the coset of `π` carries `dwz63HalfCell i k` to the `k`-th tag `π`,
`cycle · π`, `cycle⁻¹ · π`.  Uniform in `π` --- it is a group identity, not an enumeration of the
six orientations. -/
theorem dwz63_rawTag_halfCell (π : Orientation) (i k : Fin 3) :
    dwz63RawTag (dwz63HalfOrientation π i) (dwz63HalfCell i k) = dwz63HalfOrientation π k := by
  fin_cases i <;> fin_cases k <;>
    simp only [dwz63HalfOrientation, dwz63HalfCell, dwz63RawTag, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Matrix.tail_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val_succ, dwz63OrbitRotation_112,
      dwz63OrbitRotation_121, dwz63OrbitRotation_211] <;>
    first
      | rfl
      | exact dwz63_trans_one (by decide)
      | exact dwz63_trans_assoc_one (by decide)
      | exact dwz63_trans_assoc_eq (by decide)

set_option maxRecDepth 8000 in
/-- **The target address of a tag slot does not depend on the orientation.**

This is the whole content of the target-coordinate flip, on the orbit.  Within one `C₃`-coset the
three orientations all send the `k`-th tag slot to the *same* target coarse address --- so all the
letters carrying one tag have one and the same target address, hence (under target-coordinate
typicality) one and the same multiplicity `dwz63AlphaAddress` of that address. -/
theorem dwz63_halfCell_target_const (π : Orientation) (i k : Fin 3) :
    cwSquarePermute (dwz63HalfOrientation π i) (dwz63HalfCell i k)
      = cwSquarePermute π (dwz63HalfCell 0 k) := by
  revert π i k; decide

/-- The three tag slots of a coset see the three orbit cells, one each --- but each of them
*three times over*, once per orientation. -/
theorem dwz63_halfCell_target_zero (π : Orientation) :
    (({cwSquarePermute π (dwz63HalfCell 0 0), cwSquarePermute π (dwz63HalfCell 0 1),
       cwSquarePermute π (dwz63HalfCell 0 2)} : Multiset CWSquareAddress))
      = {cwSquare112, cwSquare211, cwSquare121} := by
  revert π; decide

/-! ### The obstruction, and its repair

`hasTauWeight_symSixHalf` needs the three per-tag exponents of a coset to be **equal**: a cyclic
triple consumes one letter of each of the three tags `π`, `cycle · π`, `cycle⁻¹ · π`, and the
`(1,1,2)` orbit carries no other certificate.

Under *source*-coordinate typicality they are equal.  Each tag collects one letter per orientation,
and `dwz63_rawTag_halfCell` shows those three letters come from the three *different* orbit cells,
so every tag gets `(alpha(1,1,2) + 2 alpha(1,2,1)) t` --- the count of
`Examples/DuanWuZhouLevelTwoOrbitTag.lean`.

Under *target*-coordinate typicality they are **not**.  A letter's multiplicity is now read at its
target address, and `dwz63_halfCell_target_const` says the three letters carrying one tag have one
and the same target address.  So a tag's count is `3 · alpha(that address) · t`, and by
`dwz63_halfCell_target_zero` the three tags of a coset see the three *distinct* orbit cells.  The
three counts are therefore `3 alpha(1,1,2) t`, `3 alpha(1,2,1) t`, `3 alpha(1,2,1) t`, which
`dwz63_target_halfSlotCount_ne` shows are not equal.

`dwz63HalfSlotCountOf_const` is the repair: the counts agree as soon as the target profile is
constant on the `(1,1,2)` orbit.  Replacing `dwz63AlphaAddress` on that orbit by its average ---
total orbit mass `alpha(1,1,2) + 2 alpha(1,2,1)` shared equally, which is integral at scales
divisible by `3` --- restores the equality without moving any mass off the orbit, so the bulk
exponents, the total orbit exponent and hence the whole value computation are unchanged.
-/

/-- The exponent the `k`-th tag slot of the coset of `π` receives, for a target count profile
`count`. -/
def dwz63HalfSlotCountOf (count : CWSquareAddress → ℕ) (π : Orientation) (k : Fin 3) : ℕ :=
  count (cwSquarePermute (dwz63HalfOrientation π 0) (dwz63HalfCell 0 k))
    + count (cwSquarePermute (dwz63HalfOrientation π 1) (dwz63HalfCell 1 k))
    + count (cwSquarePermute (dwz63HalfOrientation π 2) (dwz63HalfCell 2 k))

set_option maxRecDepth 20000 in
/-- Every letter a tag slot collects sits at an orbit address. -/
theorem dwz63_halfCell_target_mem_orbit (π : Orientation) (i k : Fin 3) :
    cwSquarePermute (dwz63HalfOrientation π i) (dwz63HalfCell i k) ∈ cwSquare112Orbit := by
  revert π i k; decide

/-- **The repair.**  If the target count profile is constant on the `(1,1,2)` orbit then all three
per-tag exponents of every coset agree, which is exactly the hypothesis
`hasTauWeight_symSixHalf` needs.  Nothing else about the profile is used. -/
theorem dwz63HalfSlotCountOf_const {count : CWSquareAddress → ℕ}
    (hconst : ∀ a ∈ cwSquare112Orbit, ∀ b ∈ cwSquare112Orbit, count a = count b)
    (π : Orientation) (k l : Fin 3) :
    dwz63HalfSlotCountOf count π k = dwz63HalfSlotCountOf count π l := by
  unfold dwz63HalfSlotCountOf
  have h : ∀ i m : Fin 3,
      count (cwSquarePermute (dwz63HalfOrientation π i) (dwz63HalfCell i m)) =
        count (cwSquarePermute (dwz63HalfOrientation π 0) (dwz63HalfCell 0 0)) := fun i m ↦
    hconst _ (dwz63_halfCell_target_mem_orbit π i m) _ (dwz63_halfCell_target_mem_orbit π 0 0)
  rw [h 0 k, h 1 k, h 2 k, h 0 l, h 1 l, h 2 l]

/-- The tag exponents of the target-typical profile, in closed form. -/
theorem dwz63HalfSlotCountOf_alpha (π : Orientation) (t : ℕ) (k : Fin 3) :
    dwz63HalfSlotCountOf (fun a ↦ dwz63AlphaAddress a * t) π k =
      3 * (dwz63AlphaAddress (cwSquarePermute π (dwz63HalfCell 0 k)) * t) := by
  unfold dwz63HalfSlotCountOf
  rw [dwz63_halfCell_target_const π 0 k, dwz63_halfCell_target_const π 1 k,
    dwz63_halfCell_target_const π 2 k]
  ring

/-- **`alpha` is not constant on the `(1,1,2)` orbit**, which is what makes the three per-tag
exponents of a coset differ. -/
theorem dwz63Alpha112_ne_dwz63Alpha121 : dwz63Alpha112 ≠ dwz63Alpha121 := by
  unfold dwz63Alpha112 dwz63Alpha121
  decide

/-- **The obstruction, at the identity coset.**  At any positive scale the exponent of tag `1` is
`3 alpha(1,1,2) t` and the exponent of tag `cycle` is `3 alpha(1,2,1) t`; they differ. -/
theorem dwz63_target_halfSlotCount_ne {t : ℕ} (ht : 0 < t) :
    dwz63HalfSlotCountOf (fun a ↦ dwz63AlphaAddress a * t) 1 0 ≠
      dwz63HalfSlotCountOf (fun a ↦ dwz63AlphaAddress a * t) 1 1 := by
  rw [dwz63HalfSlotCountOf_alpha, dwz63HalfSlotCountOf_alpha,
    show cwSquarePermute (1 : Orientation) (dwz63HalfCell 0 0) = cwSquare112 from by decide,
    show cwSquarePermute (1 : Orientation) (dwz63HalfCell 0 1) = cwSquare211 from by decide,
    dwz63AlphaAddress_112, dwz63AlphaAddress_211]
  unfold dwz63Alpha112 dwz63Alpha121
  omega

end Latin

/-! ## The orbit-symmetrised target profile -/

/-- **The repaired target count profile at scale `t`.**  `dwz63AlphaAddress a * t` off the
`(1,1,2)` orbit; on the orbit, the orbit's whole mass `alpha(1,1,2) + 2 alpha(1,2,1)` shared
equally between its three cells.  Integral exactly when `3 ∣ t`, which costs nothing: the stage
family already ranges over an arithmetic progression of scales. -/
noncomputable def dwz63SymCount (t : ℕ) (a : CWSquareAddress) : ℕ :=
  if a ∈ cwSquare112Orbit then (dwz63Alpha112 + 2 * dwz63Alpha121) * (t / 3)
  else dwz63AlphaAddress a * t

/-- **The repaired profile is constant on the orbit** --- the hypothesis of
`dwz63HalfSlotCountOf_const`, hence of `hasTauWeight_symSixHalf`. -/
theorem dwz63SymCount_orbit_const (t : ℕ) :
    ∀ a ∈ cwSquare112Orbit, ∀ b ∈ cwSquare112Orbit, dwz63SymCount t a = dwz63SymCount t b := by
  intro a ha b hb
  unfold dwz63SymCount
  rw [if_pos ha, if_pos hb]

/-- **The repaired profile agrees with the typical one off the orbit**, so every bulk exponent ---
and therefore the entire non-rotational half of the value computation --- is untouched. -/
theorem dwz63SymCount_off_orbit {t : ℕ} {a : CWSquareAddress} (ha : a ∉ cwSquare112Orbit) :
    dwz63SymCount t a = dwz63AlphaAddress a * t := by
  unfold dwz63SymCount
  rw [if_neg ha]

/-- **The repaired profile moves no mass off the orbit.**  At a scale divisible by `3` the three
orbit cells together still carry `(alpha(1,1,2) + 2 alpha(1,2,1)) * t`, so the total orbit exponent
`6 (alpha(1,1,2) + 2 alpha(1,2,1)) t` that the `(1,2,1)` certificate has to cover is exactly the
one the published profile produces.  The value side is therefore unchanged by the repair. -/
theorem dwz63SymCount_orbit_mass {t : ℕ} (ht : 3 ∣ t) :
    dwz63SymCount t cwSquare112 + dwz63SymCount t cwSquare121 + dwz63SymCount t cwSquare211
      = (dwz63Alpha112 + 2 * dwz63Alpha121) * t := by
  obtain ⟨u, rfl⟩ := ht
  have h112 : cwSquare112 ∈ cwSquare112Orbit := by decide
  have h121 : cwSquare121 ∈ cwSquare112Orbit := by decide
  have h211 : cwSquare211 ∈ cwSquare112Orbit := by decide
  unfold dwz63SymCount
  rw [if_pos h112, if_pos h121, if_pos h211]
  have hu : 3 * u / 3 = u := by omega
  rw [hu]
  ring

/-- **The published profile's orbit mass**, for comparison with `dwz63SymCount_orbit_mass`: the
repair really is mass-preserving on the orbit. -/
theorem dwz63AlphaAddress_orbit_mass (t : ℕ) :
    dwz63AlphaAddress cwSquare112 * t + dwz63AlphaAddress cwSquare121 * t
        + dwz63AlphaAddress cwSquare211 * t
      = (dwz63Alpha112 + 2 * dwz63Alpha121) * t := by
  rw [dwz63AlphaAddress_112, dwz63AlphaAddress_121, dwz63AlphaAddress_211]
  ring

end AlgebraicComplexity.Examples
