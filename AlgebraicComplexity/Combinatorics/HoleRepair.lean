/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Log

/-!
# Finite relabelling lemmas for repairing holes

This module formalizes the finite combinatorial core of the hole-repair theorem used by the
recursive laser method.  A family of permutations is `UniformOnParts` when a uniformly chosen
family member sends each fixed part uniformly over the part type.  Exact cardinality identities
replace division and probability throughout.

The main theorem, `exists_simultaneously_small_overlap`, is the three-leg shuffling lemma from
the hole-repair argument: one relabelling simultaneously moves the holes away from prescribed
target parts on `X`, `Y`, and `Z`, losing at most four times the mean overlap on each leg.
-/

namespace AlgebraicComplexity.HoleRepair

open scoped BigOperators

universe u v

/-! ## The seven-branch repair recurrence -/

/-- Exact budget for a recursion which consumes one broken copy at a node and then creates at
most seven smaller repair problems.  Thus `sevenBranchBudget d` is the number of nodes in the
complete seven-ary recursion tree of depth `d`. -/
def sevenBranchBudget : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + 7 * sevenBranchBudget d

@[simp] theorem sevenBranchBudget_zero : sevenBranchBudget 0 = 1 :=
  rfl

@[simp] theorem sevenBranchBudget_succ (d : ℕ) :
    sevenBranchBudget (d + 1) = 1 + 7 * sevenBranchBudget d :=
  rfl

/-- The complete seven-branch tree budget is monotone in its depth. -/
theorem sevenBranchBudget_monotone : Monotone sevenBranchBudget := by
  apply monotone_nat_of_le_succ
  intro d
  rw [sevenBranchBudget_succ]
  omega

/-- Closed-form geometric-series identity for the seven-branch budget.  Keeping this identity
division-free makes it convenient in exact finite counting arguments. -/
theorem six_mul_sevenBranchBudget_add_one (d : ℕ) :
    6 * sevenBranchBudget d + 1 = 7 ^ (d + 1) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [sevenBranchBudget_succ, pow_succ]
      omega

/-- The coarse form used in the hole-repair theorem of Duan--Wu--Zhou. -/
theorem sevenBranchBudget_le_pow (d : ℕ) :
    sevenBranchBudget d ≤ 7 ^ (d + 1) := by
  have h := six_mul_sevenBranchBudget_add_one d
  omega

/-- Solve the three-parameter seven-branch recurrence which arises after splitting a target box
into its hole/non-hole subboxes.

The three zero hypotheses say that a tensor box is empty when any one of its legs is empty.  At a
positive node, the seven recursive calls are exactly the seven Boolean masks other than the
all-non-hole mask.  Every call decreases at least one of the three depth coordinates.  The result
is deliberately independent of logarithms: clients may measure one depth unit by any certified
shrinkage operation. -/
theorem seven_branch_recurrence_le_budget
    (copies : ℕ → ℕ → ℕ → ℕ)
    (zeroX : ∀ y z, copies 0 y z = 0)
    (zeroY : ∀ x z, copies x 0 z = 0)
    (zeroZ : ∀ x y, copies x y 0 = 0)
    (step : ∀ x y z,
      copies (x + 1) (y + 1) (z + 1) ≤
        1 + copies x (y + 1) (z + 1) +
          copies (x + 1) y (z + 1) +
          copies (x + 1) (y + 1) z +
          copies x y (z + 1) +
          copies x (y + 1) z +
          copies (x + 1) y z +
          copies x y z) :
    ∀ x y z, copies x y z ≤ sevenBranchBudget (x + y + z) := by
  intro x
  induction x with
  | zero =>
      intro y z
      simp [zeroX]
  | succ x ihX =>
      intro y
      induction y with
      | zero =>
          intro z
          simp [zeroY]
      | succ y ihY =>
          intro z
          induction z with
          | zero => simp [zeroZ]
          | succ z ihZ =>
              have hX : copies x (y + 1) (z + 1) ≤
                  sevenBranchBudget (x + y + z + 2) :=
                (ihX (y + 1) (z + 1)).trans
                  (sevenBranchBudget_monotone (by omega))
              have hY : copies (x + 1) y (z + 1) ≤
                  sevenBranchBudget (x + y + z + 2) :=
                (ihY (z + 1)).trans
                  (sevenBranchBudget_monotone (by omega))
              have hZ : copies (x + 1) (y + 1) z ≤
                  sevenBranchBudget (x + y + z + 2) :=
                ihZ.trans (sevenBranchBudget_monotone (by omega))
              have hXY : copies x y (z + 1) ≤
                  sevenBranchBudget (x + y + z + 2) :=
                (ihX y (z + 1)).trans
                  (sevenBranchBudget_monotone (by omega))
              have hXZ : copies x (y + 1) z ≤
                  sevenBranchBudget (x + y + z + 2) :=
                (ihX (y + 1) z).trans
                  (sevenBranchBudget_monotone (by omega))
              have hYZ : copies (x + 1) y z ≤
                  sevenBranchBudget (x + y + z + 2) :=
                (ihY z).trans (sevenBranchBudget_monotone (by omega))
              have hXYZ : copies x y z ≤
                  sevenBranchBudget (x + y + z + 2) :=
                (ihX y z).trans (sevenBranchBudget_monotone (by omega))
              have hbudget :
                  sevenBranchBudget ((x + 1) + (y + 1) + (z + 1)) =
                    1 + 7 * sevenBranchBudget (x + y + z + 2) := by
                rw [show (x + 1) + (y + 1) + (z + 1) =
                    (x + y + z + 2) + 1 by omega]
                rfl
              have hstep := step x y z
              omega

/-- Published closed-form consequence of `seven_branch_recurrence_le_budget`. -/
theorem seven_branch_recurrence_le_pow
    (copies : ℕ → ℕ → ℕ → ℕ)
    (zeroX : ∀ y z, copies 0 y z = 0)
    (zeroY : ∀ x z, copies x 0 z = 0)
    (zeroZ : ∀ x y, copies x y 0 = 0)
    (step : ∀ x y z,
      copies (x + 1) (y + 1) (z + 1) ≤
        1 + copies x (y + 1) (z + 1) +
          copies (x + 1) y (z + 1) +
          copies (x + 1) (y + 1) z +
          copies x y (z + 1) +
          copies x (y + 1) z +
          copies (x + 1) y z +
          copies x y z)
    (x y z : ℕ) :
    copies x y z ≤ 7 ^ (x + y + z + 1) :=
  (seven_branch_recurrence_le_budget copies zeroX zeroY zeroZ step x y z).trans
    (sevenBranchBudget_le_pow (x + y + z))

/-- One multiplicative shrink reduces the natural ceiling-log depth by at least one.  This is the
discrete bridge from a cardinality estimate `b * smaller ≤ larger` to the depth coordinates used
by `seven_branch_recurrence_le_budget`. -/
theorem clog_add_one_le_of_mul_le
    {b smaller larger : ℕ} (hb : 1 < b) (hsmaller : 0 < smaller)
    (hshrink : b * smaller ≤ larger) :
    Nat.clog b smaller + 1 ≤ Nat.clog b larger := by
  have honeSmaller : 1 ≤ smaller := hsmaller
  have hbLeProduct : b ≤ b * smaller := by
    simpa only [mul_one] using Nat.mul_le_mul_left b honeSmaller
  have hlarger : 1 < larger := hb.trans_le (hbLeProduct.trans hshrink)
  have hdepthPos : 0 < Nat.clog b larger := Nat.clog_pos hb hlarger
  have htoPower : b * smaller ≤ b ^ Nat.clog b larger :=
    hshrink.trans (Nat.le_pow_clog hb larger)
  have hmulPred : b * smaller ≤ b * b ^ (Nat.clog b larger).pred := by
    calc
      b * smaller ≤ b ^ Nat.clog b larger := htoPower
      _ = b * b ^ (Nat.clog b larger).pred := by
        rw [← Nat.pow_succ']
        congr 1
        exact (Nat.succ_pred_eq_of_pos hdepthPos).symm
  have hsmallerPower : smaller ≤ b ^ (Nat.clog b larger).pred :=
    le_of_mul_le_mul_left hmulPred (Nat.zero_lt_of_lt hb)
  have hclog : Nat.clog b smaller ≤ (Nat.clog b larger).pred :=
    Nat.clog_le_of_le_pow hsmallerPower
  have hpred : (Nat.clog b larger).pred + 1 = Nat.clog b larger :=
    Nat.succ_pred_eq_of_pos hdepthPos
  omega

/-- The predecessor of a positive ceiling quotient is still strictly below the numerator after
multiplication by the denominator. -/
theorem mul_pred_ceilDiv_lt {numerator denominator : ℕ}
    (hnumerator : 0 < numerator) (hdenominator : 0 < denominator) :
    denominator * (numerator ⌈/⌉ denominator - 1) < numerator := by
  let q := numerator ⌈/⌉ denominator
  have hqPos : 0 < q := by
    by_contra hnot
    have hqZero : q = 0 := Nat.eq_zero_of_not_pos hnot
    have hle : numerator ≤ denominator * 0 :=
      (ceilDiv_le_iff_le_mul hdenominator).1 (show q ≤ 0 by omega)
    omega
  by_contra hnot
  have hnumLe : numerator ≤ denominator * (q - 1) := Nat.le_of_not_gt hnot
  have hqLe : q ≤ q - 1 := (ceilDiv_le_iff_le_mul hdenominator).2 hnumLe
  omega

/-- For a power-size interface with at most `3^n` parts, any certified lower bound `2^k ≤ n+2`
on the shrink base bounds the repair depth by the ceiling quotient `⌈2n/k⌉`. -/
theorem clog_add_two_three_pow_le_ceilDiv
    {n k : ℕ} (hk : 0 < k) (hbase : 2 ^ k ≤ n + 2) :
    Nat.clog (n + 2) (3 ^ n) ≤ (2 * n) ⌈/⌉ k := by
  have hpowBase : 1 < 2 ^ k := Nat.one_lt_pow hk.ne' Nat.one_lt_two
  have htarget : 3 ^ n ≤ 2 ^ (2 * n) := by
    calc
      3 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left (by omega) n
      _ = 2 ^ (2 * n) := by
        rw [show 4 = 2 ^ 2 by rfl, pow_mul]
  calc
    Nat.clog (n + 2) (3 ^ n) ≤ Nat.clog (2 ^ k) (2 ^ (2 * n)) :=
      Nat.clog_mono hpowBase hbase htarget
    _ = (2 * n) ⌈/⌉ k := by
      rw [Nat.clog_pow_left, Nat.clog_pow 2 (2 * n) Nat.one_lt_two]
      rw [Nat.ceilDiv_eq_add_pred_div]
      congr 1
      omega

/-- A finite family of permutations which sends every fixed part uniformly over all parts.

The subset formulation is division-free: for a fixed source part `a`, the number of relabellings
sending it into `target`, multiplied by the number of parts, equals the family size times the
cardinality of `target`. -/
structure UniformOnParts (G : Type u) (A : Type v)
    [Fintype G] [Fintype A] [DecidableEq G] [DecidableEq A] where
  relabel : G → Equiv.Perm A
  uniform_subset : ∀ (a : A) (target : Finset A),
    Fintype.card A * (Finset.univ.filter fun g ↦ relabel g a ∈ target).card =
      Fintype.card G * target.card

namespace UniformOnParts

variable {G : Type u} {A : Type v}
variable [Fintype G] [Fintype A] [DecidableEq G] [DecidableEq A]

/-- Construct subset-uniformity from the paper's pointwise statement that every source part is
sent to every target part by exactly the same fraction of relabellings. -/
def ofPointwise
    (relabel : G → Equiv.Perm A)
    (uniform_point : ∀ (a b : A),
      Fintype.card A * (Finset.univ.filter fun g ↦ relabel g a = b).card =
        Fintype.card G) : UniformOnParts G A where
  relabel := relabel
  uniform_subset := by
    classical
    intro a target
    let relation : A → G → Prop := fun b g ↦ relabel g a = b
    have hdouble :
        (∑ b ∈ target, (Finset.univ.bipartiteAbove relation b).card) =
          ∑ g ∈ (Finset.univ : Finset G), (target.bipartiteBelow relation g).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow relation
    have habove (b : A) :
        (Finset.univ.bipartiteAbove relation b).card =
          (Finset.univ.filter fun g ↦ relabel g a = b).card := by
      rfl
    have hbelow (g : G) :
        (target.bipartiteBelow relation g).card =
          if relabel g a ∈ target then 1 else 0 := by
      by_cases hg : relabel g a ∈ target
      · rw [if_pos hg]
        have heq : target.bipartiteBelow relation g = {relabel g a} := by
          ext b
          simp only [Finset.mem_bipartiteBelow, relation, Finset.mem_singleton]
          constructor
          · rintro ⟨_hb, hba⟩
            exact hba.symm
          · intro hba
            subst b
            exact ⟨hg, rfl⟩
        simp [heq]
      · rw [if_neg hg]
        have heq : target.bipartiteBelow relation g = ∅ := by
          ext b
          simp only [Finset.mem_bipartiteBelow, relation, Finset.notMem_empty, iff_false]
          rintro ⟨hb, hba⟩
          exact hg (hba ▸ hb)
        simp [heq]
    have hcount :
        (∑ b ∈ target, (Finset.univ.filter fun g ↦ relabel g a = b).card) =
          (Finset.univ.filter fun g ↦ relabel g a ∈ target).card := by
      calc
        _ = ∑ g ∈ (Finset.univ : Finset G), (target.bipartiteBelow relation g).card := by
          simpa only [habove] using hdouble
        _ = ∑ g : G, if relabel g a ∈ target then 1 else 0 := by
          simp only [hbelow]
        _ = (Finset.univ.filter fun g ↦ relabel g a ∈ target).card := by
          simp
    calc
      Fintype.card A * (Finset.univ.filter fun g ↦ relabel g a ∈ target).card =
          Fintype.card A *
            ∑ b ∈ target, (Finset.univ.filter fun g ↦ relabel g a = b).card := by
        rw [hcount]
      _ = ∑ b ∈ target,
          Fintype.card A * (Finset.univ.filter fun g ↦ relabel g a = b).card := by
        rw [Finset.mul_sum]
      _ = ∑ _b ∈ target, Fintype.card G := by
        apply Finset.sum_congr rfl
        intro b _hb
        exact uniform_point a b
      _ = Fintype.card G * target.card := by
        simp [mul_comm]

/-- The number of source parts which a relabelling sends into a prescribed target set. -/
def overlapCard (family : UniformOnParts G A)
    (target source : Finset A) (g : G) : ℕ :=
  (source.filter fun a ↦ family.relabel g a ∈ target).card

/-- `overlapCard` is the paper's intersection `|target ∩ π(source)|`. -/
theorem overlapCard_eq_card_inter_image (family : UniformOnParts G A)
    (target source : Finset A) (g : G) :
    family.overlapCard target source g =
      (target ∩ source.image (family.relabel g)).card := by
  classical
  have himage :
      (source.filter fun a ↦ family.relabel g a ∈ target).image (family.relabel g) =
        target ∩ source.image (family.relabel g) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨b, ⟨hbSource, hbTarget⟩, rfl⟩
      exact ⟨hbTarget, ⟨b, hbSource, rfl⟩⟩
    · rintro ⟨haTarget, b, hbSource, hba⟩
      exact ⟨b, ⟨hbSource, hba ▸ haTarget⟩, hba⟩
  rw [overlapCard, ← himage]
  exact (Finset.card_image_of_injective _ (family.relabel g).injective).symm

/-- Exact first moment of the overlap count. -/
theorem card_mul_sum_overlapCard (family : UniformOnParts G A)
    (target source : Finset A) :
    Fintype.card A * ∑ g : G, family.overlapCard target source g =
      Fintype.card G * target.card * source.card := by
  classical
  let relation : A → G → Prop := fun a g ↦ family.relabel g a ∈ target
  have hdouble :
      (∑ a ∈ source, (Finset.univ.bipartiteAbove relation a).card) =
        ∑ g ∈ (Finset.univ : Finset G), (source.bipartiteBelow relation g).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow relation
  have habove (a : A) :
      (Finset.univ.bipartiteAbove relation a).card =
        (Finset.univ.filter fun g ↦ family.relabel g a ∈ target).card := by
    rfl
  have hbelow (g : G) :
      (source.bipartiteBelow relation g).card = family.overlapCard target source g := by
    simp [Finset.bipartiteBelow, relation, overlapCard]
  have hdouble' :
      (∑ a ∈ source, (Finset.univ.bipartiteAbove relation a).card) =
        ∑ g : G, family.overlapCard target source g := by
    simpa only [hbelow, Finset.sum_const_zero] using hdouble
  calc
    Fintype.card A * ∑ g : G, family.overlapCard target source g =
        Fintype.card A *
          ∑ a ∈ source, (Finset.univ.bipartiteAbove relation a).card := by
            rw [hdouble']
    _ = ∑ a ∈ source,
          Fintype.card A * (Finset.univ.bipartiteAbove relation a).card := by
            rw [Finset.mul_sum]
    _ = ∑ _a ∈ source, Fintype.card G * target.card := by
            apply Finset.sum_congr rfl
            intro a _ha
            rw [habove]
            exact family.uniform_subset a target
    _ = Fintype.card G * target.card * source.card := by
            simp [mul_comm, mul_left_comm]

/-- Relabellings whose overlap is more than four times its exact mean, written without division. -/
def badRelabelings (family : UniformOnParts G A)
    (target source : Finset A) : Finset G :=
  Finset.univ.filter fun g ↦
    4 * target.card * source.card < Fintype.card A * family.overlapCard target source g

/-- At most one quarter of a uniform relabelling family has overlap exceeding four times the
mean.  This is the exact finite Markov inequality used in the hole-repair proof. -/
theorem four_mul_card_badRelabelings_le (family : UniformOnParts G A)
    (target source : Finset A) :
    4 * (family.badRelabelings target source).card ≤ Fintype.card G := by
  classical
  by_cases hzero : target.card * source.card = 0
  · have hoverlap : ∀ g : G, family.overlapCard target source g = 0 := by
      intro g
      rcases Nat.mul_eq_zero.mp hzero with htarget | hsource
      · have : target = ∅ := Finset.card_eq_zero.mp htarget
        simp [overlapCard, this]
      · have : source = ∅ := Finset.card_eq_zero.mp hsource
        simp [overlapCard, this]
    have hbad : family.badRelabelings target source = ∅ := by
      ext g
      simp [badRelabelings, hoverlap]
    simp [hbad]
  · have hpositive : 0 < target.card * source.card := Nat.pos_of_ne_zero hzero
    by_cases hbadEmpty : (family.badRelabelings target source).card = 0
    · simp [hbadEmpty]
    · have hbadNonempty : (family.badRelabelings target source).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero hbadEmpty)
      have hstrict :
          (family.badRelabelings target source).card *
              (4 * target.card * source.card) <
            ∑ g ∈ family.badRelabelings target source,
              Fintype.card A * family.overlapCard target source g := by
        rw [show (family.badRelabelings target source).card *
              (4 * target.card * source.card) =
            ∑ _g ∈ family.badRelabelings target source,
              (4 * target.card * source.card) by simp]
        exact Finset.sum_lt_sum_of_nonempty hbadNonempty fun g hg ↦ by
          exact (Finset.mem_filter.mp hg).2
      have hsubset : family.badRelabelings target source ⊆ (Finset.univ : Finset G) := by
        exact Finset.subset_univ _
      have hsumLe :
          (∑ g ∈ family.badRelabelings target source,
              Fintype.card A * family.overlapCard target source g) ≤
            ∑ g : G, Fintype.card A * family.overlapCard target source g := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ ↦ Nat.zero_le _)
      have htotal :
          (∑ g : G, Fintype.card A * family.overlapCard target source g) =
            Fintype.card G * target.card * source.card := by
        rw [← Finset.mul_sum, family.card_mul_sum_overlapCard]
      have hproduct :
          (4 * (family.badRelabelings target source).card) *
              (target.card * source.card) <
            Fintype.card G * (target.card * source.card) := by
        calc
          (4 * (family.badRelabelings target source).card) *
                (target.card * source.card) =
              (family.badRelabelings target source).card *
                (4 * target.card * source.card) := by
                  simp [mul_assoc, mul_comm, mul_left_comm]
          _ < ∑ g ∈ family.badRelabelings target source,
                Fintype.card A * family.overlapCard target source g := hstrict
          _ ≤ ∑ g : G, Fintype.card A * family.overlapCard target source g := hsumLe
          _ = Fintype.card G * (target.card * source.card) := by
                simpa [mul_assoc] using htotal
      exact le_of_mul_le_mul_right hproduct.le hpositive

end UniformOnParts

section ThreeLegs

variable {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G]
variable {X Y Z : Type v}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- Three-leg finite shuffling lemma.

For prescribed target and hole sets on each tensor leg, a single member of a common uniform
relabeling family has overlap at most four times the exact mean on all three legs.  This is the
division-free content of Lemma 3.1 in *New Bounds for Matrix Multiplication: From Alpha to Omega*
and is the reusable combinatorial heart of its hole-repair theorem. -/
theorem exists_simultaneously_small_overlap
    (familyX : UniformOnParts G X)
    (familyY : UniformOnParts G Y)
    (familyZ : UniformOnParts G Z)
    (targetX holesX : Finset X)
    (targetY holesY : Finset Y)
    (targetZ holesZ : Finset Z) :
    ∃ g : G,
      Fintype.card X * familyX.overlapCard targetX holesX g ≤
          4 * targetX.card * holesX.card ∧
      Fintype.card Y * familyY.overlapCard targetY holesY g ≤
          4 * targetY.card * holesY.card ∧
      Fintype.card Z * familyZ.overlapCard targetZ holesZ g ≤
          4 * targetZ.card * holesZ.card := by
  classical
  let badX := familyX.badRelabelings targetX holesX
  let badY := familyY.badRelabelings targetY holesY
  let badZ := familyZ.badRelabelings targetZ holesZ
  let bad := (badX ∪ badY) ∪ badZ
  have hx : 4 * badX.card ≤ Fintype.card G :=
    familyX.four_mul_card_badRelabelings_le targetX holesX
  have hy : 4 * badY.card ≤ Fintype.card G :=
    familyY.four_mul_card_badRelabelings_le targetY holesY
  have hz : 4 * badZ.card ≤ Fintype.card G :=
    familyZ.four_mul_card_badRelabelings_le targetZ holesZ
  have hbadCard : bad.card ≤ badX.card + badY.card + badZ.card := by
    dsimp [bad]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hfour : 4 * bad.card ≤ 3 * Fintype.card G := by
    omega
  have hGpos : 0 < Fintype.card G := Fintype.card_pos
  have hbadLt : bad.card < (Finset.univ : Finset G).card := by
    simp only [Finset.card_univ]
    omega
  obtain ⟨g, _hgUniv, hgBad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbadLt
  have hgX : g ∉ badX := by
    intro hg
    apply hgBad
    exact Finset.mem_union_left badZ (Finset.mem_union_left badY hg)
  have hgY : g ∉ badY := by
    intro hg
    apply hgBad
    exact Finset.mem_union_left badZ (Finset.mem_union_right badX hg)
  have hgZ : g ∉ badZ := by
    intro hg
    apply hgBad
    exact Finset.mem_union_right (badX ∪ badY) hg
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa [badX, UniformOnParts.badRelabelings] using hgX
  · simpa [badY, UniformOnParts.badRelabelings] using hgY
  · simpa [badZ, UniformOnParts.badRelabelings] using hgZ

end ThreeLegs

end AlgebraicComplexity.HoleRepair
