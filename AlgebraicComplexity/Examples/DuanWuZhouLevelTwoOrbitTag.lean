/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquareSymmetry
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSixOrientationValues

/-!
# The `(1,1,2)`-orbit tag of a six-orientation letter

In the asymmetric bypass a retained constituent is the external product, in word order, of `6n`
*oriented* cells: for each of the six leg permutations `o` and each of the `n` positions `i`, one
factor `permute o (T_{s (o,i)})` with `s (o,i)` a coarse square address.  The six orientations are
independent cells, so the letters are general words, not the diagonal ones of
`Examples/DuanWuZhouLevelTwoSixOrientationValues.lean`.

Twelve of the fifteen coarse addresses carry a non-rotational `tau`-weight, and
`hasTauWeight_permute_iff` makes the orientation irrelevant for them.  The three addresses of the
`(1,1,2)` orbit do not: only the *three-symmetrized* value is available, so their oriented letters
must be regrouped into cyclic triples before any certificate applies.  This module is the
bookkeeping that makes that regrouping canonical.

## The tag

`cwSquareConstituent_211_isomorphic_cycle` and `cwSquareConstituent_121_isomorphic_cycleSymm`
exhibit the two other orbit constituents as the two rotations of `T_{1,1,2}`.  Writing
`rot s` for that rotation (`dwz63OrbitRotation`), an oriented orbit letter is

`permute o (T_s) ≅ permute o (permute (rot s) T_{1,1,2}) = permute ((rot s).trans o) T_{1,1,2}`,

so it is determined by the single group element `dwz63RawTag o s = (rot s).trans o` of
`Orientation = Equiv.Perm Leg`.

**Transport convention.**  The `o`-th component of a `symSixPartition` label lives in
`PermutedBlockIndex e_o`, and the count lane's `dwz63SourceLetter o` transports it back to a
*source* coarse address along `(permuteBlockAddress e_o).symm`; the oriented constituent at
`(o, i)` is therefore `permute e_o (T_{dwz63SourceLetter o (label i)})`.  `dwz63RawTag` is
computed on that **source** letter, which is exactly the `s` of
`isomorphic_permute_dwz63OrbitConstituent`.  Typicality is the count lane's
`Dwz63OrientationTypical` (`Examples/DuanWuZhouLevelTwoOrientationTypical.lean`): each of the six
oriented sub-words has `WordType.multiplicity` equal to `proportionalCounts dwz63AlphaAddress t`,
with `dwz63OrientationTypical_length` supplying `n + 1 = 10 ^ 8 * t`.  The tag is the **full** permutation `g ∈ S₃`; no symmetry of `T_{1,1,2}` is
used and none is available (`Isomorphic (T_{1,1,2}) (permute swapXY (T_{1,1,2}))` is not in the
repository).  Each of the six tags carries `(alpha(1,1,2) + 2 alpha(1,2,1)) t` oriented letters,
and each `C₃`-coset `{π, cycle·π, cycle⁻¹·π}` of tags assembles into `permute π (sym₃ T_{1,1,2})`
(`permute_symThree_eq`), whose weight is the `sym₃` certificate's by `HasTauWeight.permute`.

## The count

Summed over the six orientations and the three orbit addresses with masses `a` on `(1,1,2)` and
`c` on each of `(1,2,1)`, `(2,1,1)`, every one of the six full tags receives exactly `a + 2 c`
oriented letters (`Examples/DuanWuZhouLevelTwoOrbitCounting.lean`), so the two `C₃`-cosets give
`2 (a + 2 c)` triples in total.

At the typical word, `a = alpha(1,1,2) t` and `c = alpha(1,2,1) t`, so there are
`2 (alpha(1,1,2) + 2 alpha(1,2,1)) t` triples.  Of these, `2 alpha(1,1,2) t` are certified by the
`b`-split chain (`Examples/DuanWuZhouLevelTwoLeafTauWeight.lean`, value `V_{1,1,2}` per position,
hence `V_{1,1,2} ^ (6 alpha(1,1,2) t)` in total) and the remaining `4 alpha(1,2,1) t` by the
`beta`-split chain (`...LeafTauWeightBeta.lean`, giving `V_{1,2,1} ^ (12 alpha(1,2,1) t)`).
`dwz63_orbitTriple_split` records that the two counts add up.

## The value target

`dwz63_exp_logVal_pow_six_mul`: with `n = 10 ^ 8 * t`, the endpoint's
`Real.exp dwz63LogVal ^ (6 * n)` is the `6 t`-th power of the `alpha`-weighted product of the
fifteen component values.  Combined with the tag count this is exactly

`prod_{s not in orbit} V_s ^ (6 alpha(s) t) * V_{1,1,2} ^ (6 alpha(1,1,2) t)
   * V_{1,2,1} ^ (12 alpha(1,2,1) t)`.

## Assembly

`MatrixMultiplication/WordTensorReindex.lean`'s `hasTauWeight_wordTensor_append_three` takes the
three blocks --- the non-rotational bulk, the `b`-class triples and the `beta`-class triples ---
and multiplies their weights, with `Isomorphic.positiveSupportWordTensor_of_same_type` reordering
the retained word into that shape.  The two orbit blocks are supplied by
`dwz63_hasTauWeight_power_permute_symThree_112` and `..._121` below, one per tag.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

noncomputable section

/-! ## The orbit rotation -/

/-- The rotation exhibiting an orbit address as a leg permutation of `(1,1,2)`:
`(1,1,2) ↦ 1`, `(2,1,1) ↦ cycle`, `(1,2,1) ↦ cycle⁻¹`.  Off the orbit the value is unused. -/
def dwz63OrbitRotation (s : CWSquareAddress) : Orientation :=
  if s = cwSquareAddress 2 1 1 then cycle
  else if s = cwSquareAddress 1 2 1 then cycle.symm
  else 1

@[simp] theorem dwz63OrbitRotation_112 : dwz63OrbitRotation cwSquare112 = 1 := by
  simp [dwz63OrbitRotation]

@[simp] theorem dwz63OrbitRotation_211 : dwz63OrbitRotation cwSquare211 = cycle := by
  simp [dwz63OrbitRotation]

@[simp] theorem dwz63OrbitRotation_121 : dwz63OrbitRotation cwSquare121 = cycle.symm := by
  simp [dwz63OrbitRotation]

/-- `permute 1` is the identity, stated abstractly so that no client ever has to reduce a
concrete constituent to weak head normal form. -/
theorem isomorphic_permute_one {K : Type u} [CommSemiring K] {V : Leg → Type*}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)] (T : Tensor3 K V) :
    Isomorphic T (Tensor.permute (1 : Orientation) T) := by
  refine Isomorphic.of_eq ?_
  show _ = Tensor.permute (Equiv.refl Leg) T
  rw [Tensor.permute_refl]
  rfl

variable (K : Type u) [CommRing K]

/-- **Every orbit constituent is a rotation of the `(1,1,2)` constituent.**

The two nontrivial cases are the committed `cwSquareConstituent_211_isomorphic_cycle` and
`cwSquareConstituent_121_isomorphic_cycleSymm`. -/
theorem isomorphic_dwz63OrbitConstituent_112 :
    Isomorphic ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)
      (Tensor.permute (dwz63OrbitRotation cwSquare112)
        ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)) := by
  rw [dwz63OrbitRotation_112]
  exact isomorphic_permute_one _

theorem isomorphic_dwz63OrbitConstituent_211 :
    Isomorphic ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare211)
      (Tensor.permute (dwz63OrbitRotation cwSquare211)
        ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)) := by
  rw [dwz63OrbitRotation_211]
  exact cwSquareConstituent_211_isomorphic_cycle K dwz63Q

theorem isomorphic_dwz63OrbitConstituent_121 :
    Isomorphic ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare121)
      (Tensor.permute (dwz63OrbitRotation cwSquare121)
        ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)) := by
  rw [dwz63OrbitRotation_121]
  exact cwSquareConstituent_121_isomorphic_cycleSymm K dwz63Q

/-! ## The raw tag and its even representative -/

/-- The raw tag of an oriented orbit letter: the group element `g` with
`permute o (T_s) ≅ permute g (T_{1,1,2})`. -/
def dwz63RawTag (o : Orientation) (s : CWSquareAddress) : Orientation :=
  (dwz63OrbitRotation s).trans o

/-- **The oriented orbit letter is the raw tag's rotation of `T_{1,1,2}`.** -/
theorem isomorphic_permute_dwz63OrbitConstituent
    (o : Orientation) (s : CWSquareAddress)
    (h : Isomorphic ((cwSquarePartitionedTensor K dwz63Q).constituent s)
      (Tensor.permute (dwz63OrbitRotation s)
        ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112))) :
    Isomorphic (Tensor.permute o ((cwSquarePartitionedTensor K dwz63Q).constituent s))
      (Tensor.permute (dwz63RawTag o s)
        ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)) :=
  (h.permute_legs o).trans
    (Isomorphic.of_eq
      (Tensor.permute_apply_trans (dwz63OrbitRotation s) o
        ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)).symm)

/-- **`permute π (sym₃ T)` is the external product of the three `C₃`-coset rotations.**

`sym₃` is an external product of leg permutations, permuting an external product is factorwise
(`Tensor.permute_external`) and composing two permutations is one permutation
(`Tensor.permute_apply_trans`).  This is the exact analogue of
`symSix_eq_sixOrientationProduct`, and it is an *equality*, not merely an isomorphism.

It is the whole content of the tagging: the three oriented orbit letters whose full tags form the
`C₃`-coset `{π, cycle·π, cycle⁻¹·π}` assemble, in this association, into `permute π (sym₃ T)`. -/
theorem permute_symThree_eq {K : Type u} [CommSemiring K] {V : Leg → Type v}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)] (π : Orientation) (T : Tensor3 K V) :
    Tensor.permute π (symThree K T) =
      Tensor.external
        (Tensor.external (Tensor.permute π T) (Tensor.permute (cycle.trans π) T))
        (Tensor.permute (cycle.symm.trans π) T) := by
  unfold symThree
  rw [Tensor.permute_external, Tensor.permute_external, Tensor.permute_apply_trans,
    Tensor.permute_apply_trans]
  rfl

/-- **One `C₃`-coset of oriented letters carries the `sym₃` certificate weight.**

No symmetry of `T` is used: the weight of `sym₃ T` survives the leg permutation `π`
(`HasTauWeight.permute`), and `permute_symThree_eq` identifies the permuted object with the
triple. -/
theorem hasTauWeight_permute_symThree_triple {K : Type u} [CommSemiring K] {V : Leg → Type v}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)] {T : Tensor3 K V} {τ w : ℝ}
    (h : HasTauWeight K (symThree K T) τ w) (π : Orientation) :
    HasTauWeight K
      (Tensor.external
        (Tensor.external (Tensor.permute π T) (Tensor.permute (cycle.trans π) T))
        (Tensor.permute (cycle.symm.trans π) T)) τ w := by
  have hp := h.permute π
  rwa [permute_symThree_eq] at hp

/-- **A block of `n+1` `C₃`-cosets at the same tag carries the powered `sym₃` weight.**

This is the shape the two orbit certificates come in: they bound
`Tensor.power (sym₃ T_{1,1,2}) (Mass · k)`, i.e. `Mass · k` triples at once.  Transporting by `π`
costs nothing, so the same certificate serves every one of the six tags. -/
theorem hasTauWeight_power_permute_symThree {K : Type u} [CommSemiring K] {V : Leg → Type v}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)] {T : Tensor3 K V} {τ w : ℝ} {n : ℕ}
    (h : HasTauWeight K (Tensor.power (symThree K T) (n + 1)) τ w) (π : Orientation) :
    HasTauWeight K (Tensor.power (Tensor.permute π (symThree K T)) (n + 1)) τ w :=
  (h.permute π).of_restricts
    (Tensor.Isomorphic.power_permute_positive_unbundled (symThree K T) n π).restricts

end

/-! ## The tag count -/

section Count

/-- The mass of an orbit address in the typical word, with `a` on `(1,1,2)` and `c` on each of the
two rotations. -/
def dwz63OrbitMass (a c : ℕ) (s : CWSquareAddress) : ℕ :=
  if s = cwSquareAddress 1 1 2 then a else c

/-- **The six-raw-tag partition.**

For a fixed tag `π` and a fixed orbit cell `s` there is exactly one orientation carrying that
cell to that tag, namely `(rot s)⁻¹ · π`.  This is pure cancellation in `Equiv.Perm Leg` --- no
enumeration of the six orientations and no `decide` --- and it is what makes the tag count
uniform: each of the six tags receives one letter per orbit cell.

`ELABORATION NOTE:` `Tensor.orientation_eq_six` is deliberately *not* used.  The eighteen tag
computations are unnecessary because the statement is a group cancellation, so the tiny-closed-fact
case analysis of `DESIGN.md`:735 does not arise. -/
theorem dwz63_rawTag_existsUnique (π : Orientation) (s : CWSquareAddress) :
    ∃! o : Orientation, dwz63RawTag o s = π := by
  refine ⟨(dwz63OrbitRotation s).symm.trans π, ?_, ?_⟩
  · show (dwz63OrbitRotation s).trans ((dwz63OrbitRotation s).symm.trans π) = π
    rw [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]
  · intro o ho
    have ho' : (dwz63OrbitRotation s).trans o = π := ho
    rw [← ho', ← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]

/-- **The mass one tag collects from the three orbit cells is `a + 2 c`.**

Combined with `dwz63_rawTag_existsUnique` --- one orientation per (tag, cell) pair --- this is the
per-tag letter count under per-orientation typicality: with `a = alpha(1,1,2) t` and
`c = alpha(1,2,1) t`, every one of the six tags carries `(alpha(1,1,2) + 2 alpha(1,2,1)) t`
oriented letters. -/
theorem dwz63_orbitMass_sum (a c : ℕ) :
    ∑ s ∈ cwSquare112Orbit, dwz63OrbitMass a c s = a + 2 * c := by
  rw [cwSquare112Orbit, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [dwz63OrbitMass, if_true,
    if_neg (by decide : ¬ (cwSquareAddress 1 2 1 = cwSquareAddress 1 1 2)),
    if_neg (by decide : ¬ (cwSquareAddress 2 1 1 = cwSquareAddress 1 1 2))]
  ring

/-- **The two `C₃`-cosets give `2 (a + 2 c)` triples.**

The six tags split into the two cosets `{π, π·cycle, π·cycle⁻¹}`; each coset's `3 (a + 2 c)`
letters partition into `a + 2 c` cyclic triples, so there are `2 (a + 2 c)` triples in all --- the
number `dwz63_orbitTriple_split` then divides between the two certificates. -/
theorem dwz63_orbitTag_coset_triples (a c : ℕ) :
    2 * (a + 2 * c) = 6 * (a + 2 * c) / 3 := by
  omega

/-- **The two certificates cover the triples exactly.**

`2 a` triples are certified by the `b`-split chain (three positions each, so `6 a` oriented
letters at value `V_{1,1,2}`) and `4 c` by the `beta`-split chain (`12 c` at `V_{1,2,1}`);
together they are the `2 (a + 2 c)` triples the tag count produces. -/
theorem dwz63_orbitTriple_split (a c : ℕ) : 2 * a + 4 * c = 2 * (a + 2 * c) := by ring

/-- The total oriented orbit mass is `6 (a + 2 c)`, i.e. three even tags of `2 (a + 2 c)` each. -/
theorem dwz63_orbitTag_total (a c : ℕ) : 6 * (a + 2 * c) = 3 * (2 * (a + 2 * c)) := by ring

end Count

/-! ## The two orbit certificates, at every tag -/

section Certificates

variable (K : Type u) [Field K]

/-- **The `b`-class block, at an arbitrary tag.**

`exists_eventually_dwz112ConstituentHasTauWeight` bounds `sym₃` of the coarse `(1,1,2)`
constituent raised to `dwz112Mass * k`; `hasTauWeight_power_permute_symThree` carries it to the
tag `π` at no cost.  One such block covers `dwz112Mass * k` of the `2 alpha(1,1,2) t` `b`-triples. -/
theorem dwz63_hasTauWeight_power_permute_symThree_112 (π : Orientation) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power
          (Tensor.permute π
            (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)))
          (dwz112Mass * k))
        dwz63Tau (dwz112LeafTerm K ^ (3 * (dwz112Mass * k))) := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz112ConstituentHasTauWeight K
  refine ⟨max N 1, fun k hk ↦ ?_⟩
  have hk1 : 0 < k := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right N 1) hk)
  have hpos : 0 < dwz112Mass * k := Nat.mul_pos (by norm_num [dwz112Mass_eq]) hk1
  obtain ⟨n, hn⟩ : ∃ n, dwz112Mass * k = n + 1 := ⟨dwz112Mass * k - 1, by omega⟩
  have h := hN k (le_trans (le_max_left N 1) hk)
  rw [hn] at h ⊢
  exact hasTauWeight_power_permute_symThree h π

/-- **The `beta`-class block, at an arbitrary tag.**  Same statement at the free split. -/
theorem dwz63_hasTauWeight_power_permute_symThree_121 (π : Orientation) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power
          (Tensor.permute π
            (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)))
          (dwz121Mass * k))
        dwz63Tau (dwz121LeafTerm K ^ (3 * (dwz121Mass * k))) := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz121ConstituentHasTauWeight K
  refine ⟨max N 1, fun k hk ↦ ?_⟩
  have hk1 : 0 < k := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right N 1) hk)
  have hpos : 0 < dwz121Mass * k := Nat.mul_pos (by norm_num [dwz121Mass_eq]) hk1
  obtain ⟨n, hn⟩ : ∃ n, dwz121Mass * k = n + 1 := ⟨dwz121Mass * k - 1, by omega⟩
  have h := hN k (le_trans (le_max_left N 1) hk)
  rw [hn] at h ⊢
  exact hasTauWeight_power_permute_symThree h π

end Certificates

/-! ## The value target at a typical word -/

/-- **One period of the endpoint's value target, in the six-orientation exponent.**

The bypass hypothesis is `Real.exp dwz63LogVal ^ (6 * (len j + 1))` with
`len j + 1 = 10 ^ 8 * t`.  By `dwz63_exp_logVal_pow_eq_prod` that is the `6 t`-th power of the
`alpha`-weighted product of the fifteen component values, which is what the tag count and the
twelve non-rotational weights assemble to. -/
theorem dwz63_exp_logVal_pow_six_mul (t : ℕ) :
    Real.exp dwz63LogVal ^ (6 * (100000000 * t)) =
      (∏ j : Fin 15, dwz63Val j ^ dwz63Alpha j) ^ (6 * t) := by
  rw [← dwz63_exp_logVal_pow_eq_prod, ← pow_mul]
  congr 1
  ring

end AlgebraicComplexity.Examples
