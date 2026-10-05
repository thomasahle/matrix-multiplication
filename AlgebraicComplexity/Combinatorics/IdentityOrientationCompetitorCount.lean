/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalWordTypeMultinomial
import AlgebraicComplexity.Combinatorics.PushedProfileTypeCounting

/-!
# Cellwise competitor counts for a single fixed orientation

This module proves the finite counting statement behind the "Claim 6.18" half of the
quotient-feature counting condition (`hyp:quotient-count` in `better_bound/paper.tex`): for a
*fixed* coarse split sequence, the compatible fine blocks are counted **cell by cell**, and the
cells are the fibers of a finite *compatibility-cell map* on the split alphabet.

## The situation being axiomatized

In the source argument (`papers/2404.16349v3`, `constituent.tex` lines 406--432) compatibility of a
level-`1` block `Y_Ĵ` with a fixed level-`(ℓ-1)` block triple is equivalent to a family of *split
equalities*, one for each member of

```
{ S_{t, i', j', 0} }_{t, i', j'}   ∪   { S_{t, *, j', +} }_{t, j'},
```

which is a **partition** of the coordinates of the first region.  Its boundary cells
`S_{t,i',j',0}` are singletons of the split alphabet and its pooled cells `S_{t,*,j',+}` are
unions.

The orbit lemmas in this file count an **unlabelled set of split states**.  Consequently a
self-complementary fixed point occurs once.  They must not be used for the paper interface's two
labelled child occurrences: there the left and right occurrences remain distinct even when their
child states agree, so the mass is `2 * α(u)`.  That occurrence-correct construction is formalized
in `ComplementaryOccurrenceDefs`, `ComplementaryOccurrenceCell`, and
`ComplementaryOccurrenceCounting`.

**Why a single orientation makes this separable.**  A certificate that uses one fixed orientation
for every region has a *constant* per-region orientation, so the complementation `dual` and the
cell map `cellMap` do not vary from coordinate to coordinate: the whole compatibility constraint
is a single conditional word type over one product alphabet `Cell × Feature`, and its count
factors over cells.  Nothing in this file mentions orientations; that is precisely the content of
the reduction.  A repeated-orientation client must supply a coordinate-dependent cell map before
it can use these theorems.

## Main results

* `sum_dualInvariant_eq_sum_representatives` --- an unlabelled orbit-sum formula.  A profile
  summed over a complementation-closed set equals the sum over orbit representatives, with fixed
  points contributing once.
* `mappedType_apply_of_complementary_pair` --- the corresponding unlabelled two-state-fiber case.
* `multinomial_eq_multinomial_mappedType_fst_mul_prod` --- the chain rule for multinomial
  coefficients over a product alphabet; generic and division-free.
* `card_conditionalTypeClass_eq_prod_multinomial` --- **the loss-free cellwise count**: for a
  fixed coarse word the number of compatible fine words is *exactly* the product over cells of
  the per-cell multinomial coefficient.  The source only claims `≤ 2^{...} ± o(n)`; the exact
  identity is available because the conditional method of types is division-free here.
* `conditionalProfileEntropyBase_eq_prod_cellBase` --- a generic factorization of the
  conditional-entropy base as `∏_c exp(w_c · H(γ_c))`.  The occurrence-correct modules supply
  the paper's cell masses.
* `card_proportionalConditionalTypeClass_le_loss_mul_prod_cellBase_pow` --- the sequence-facing
  `subexponential loss × base ^ k` form with the base displayed as that cell product.
* `Growth.Subexponential.finset_sup'`, `card_le_sup'_mul_sup'_pow`, and
  `card_proportionalConditionalTypeClass_le_sup'_loss_mul_sup'_base_pow` --- uniformity over the
  finitely many certificate nodes: one bound valid at every node, whose loss is still
  subexponential.

## Interface for the compatibility-isolation client

`MatrixMultiplication/CompatibilityIsolationCounting.lean` already reduces a competitor set to a
conditional type class through
`ConditionalCompetitorEncoding.card_competitors_le_card_conditionalTypeClass`.  Every theorem
below is stated about `WordType.conditionalTypeClass`, so that reduction composes directly and
**no adapter is required on the client side**.

## Position in the library

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  Only finite alphabets, integral profiles,
multinomial coefficients, and real entropy appear; there is no tensor, no orientation, and no
numerical bound.
-/

open scoped BigOperators

namespace AlgebraicComplexity

namespace Growth

/-- The pointwise supremum of a finite family of subexponential losses is subexponential.  This
is the packaging consumed when a bound has to hold uniformly over the finitely many nodes of a
certificate. -/
theorem Subexponential.finset_sup' {Node : Type*} [DecidableEq Node]
    (nodes : Finset Node) (hne : nodes.Nonempty) (loss : Node → ℕ → ℝ)
    (hloss : ∀ node ∈ nodes, Subexponential (loss node)) :
    Subexponential (fun k ↦ nodes.sup' hne fun node ↦ loss node k) := by
  classical
  have hsum : Subexponential (fun k ↦ ∑ node ∈ nodes, loss node k) :=
    Subexponential.finset_sum nodes loss hloss
  refine Subexponential.mono hsum ?_ ?_
  · intro k
    obtain ⟨node, hnode⟩ := hne
    exact le_trans ((hloss node hnode).nonneg k)
      (Finset.le_sup' (fun m ↦ loss m k) hnode)
  · intro k
    refine Finset.sup'_le hne _ fun node hnode ↦ ?_
    exact Finset.single_le_sum (f := fun m ↦ loss m k)
      (fun m hm ↦ (hloss m hm).nonneg k) hnode

end Growth

namespace WordType

universe u v w

/-! ## The entropy form of the cell product -/

section Entropy

/-- Mass-weighted profile entropy written without division by the mass.  The zero-mass case is
covered: a profile of zero total mass is identically zero. -/
theorem profileMass_mul_profileEntropyNats {I : Type u} [Fintype I] (a : I → ℕ) :
    (profileMass a : ℝ) * profileEntropyNats a =
      ∑ i, -(a i : ℝ) * Real.log ((a i : ℝ) / (profileMass a : ℝ)) := by
  classical
  unfold profileEntropyNats
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos (profileMass a) with hmass | hmass
  · have hle : a i ≤ profileMass a :=
      Finset.single_le_sum (f := a) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hzero : a i = 0 := by omega
    simp [hmass, hzero, Real.negMulLog]
  · have hmassR : ((profileMass a : ℝ)) ≠ 0 := by exact_mod_cast hmass.ne'
    rw [Real.negMulLog, ← mul_assoc]
    refine congrArg (· * Real.log ((a i : ℝ) / (profileMass a : ℝ))) ?_
    field_simp

variable {C : Type u} {F : Type v} [Fintype C] [Fintype F]

/-- One cell of the entropy identity: relative to the total mass `M`, the joint contribution of a
cell plus the cell's own entropy term is the cell-conditional contribution. -/
private theorem cell_entropy_term (M : ℕ) (row : F → ℕ) (hM : profileMass row ≤ M) :
    (∑ f, -(row f : ℝ) * Real.log ((row f : ℝ) / (M : ℝ))) +
        (profileMass row : ℝ) * Real.log ((profileMass row : ℝ) / (M : ℝ)) =
      ∑ f, -(row f : ℝ) * Real.log ((row f : ℝ) / (profileMass row : ℝ)) := by
  classical
  have hmassSum : ∑ f, (row f : ℝ) = (profileMass row : ℝ) := by
    simp only [profileMass, Nat.cast_sum]
  rcases Nat.eq_zero_or_pos (profileMass row) with hw | hw
  · have hzero : ∀ f, row f = 0 := by
      intro f
      have hle : row f ≤ profileMass row :=
        Finset.single_le_sum (f := row) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ f)
      omega
    simp [hw, hzero]
  · have hwR : ((profileMass row : ℝ)) ≠ 0 := by exact_mod_cast hw.ne'
    have hMpos : 0 < M := lt_of_lt_of_le hw hM
    have hMR : ((M : ℝ)) ≠ 0 := by exact_mod_cast hMpos.ne'
    have hterm : ∀ f : F,
        -(row f : ℝ) * Real.log ((row f : ℝ) / (M : ℝ)) =
          -(row f : ℝ) * Real.log ((row f : ℝ) / (profileMass row : ℝ)) -
            (row f : ℝ) * Real.log ((profileMass row : ℝ) / (M : ℝ)) := by
      intro f
      rcases Nat.eq_zero_or_pos (row f) with hf | hf
      · simp [hf]
      · have hfR : (0 : ℝ) < (row f : ℝ) := by exact_mod_cast hf
        have hwPos : (0 : ℝ) < (profileMass row : ℝ) := by exact_mod_cast hw
        have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
        have hsplit : (row f : ℝ) / (M : ℝ) =
            ((row f : ℝ) / (profileMass row : ℝ)) *
              ((profileMass row : ℝ) / (M : ℝ)) := by
          field_simp
        rw [hsplit, Real.log_mul (by positivity) (by positivity)]
        ring
    calc
      (∑ f, -(row f : ℝ) * Real.log ((row f : ℝ) / (M : ℝ))) +
            (profileMass row : ℝ) * Real.log ((profileMass row : ℝ) / (M : ℝ))
          = (∑ f, (-(row f : ℝ) * Real.log ((row f : ℝ) / (profileMass row : ℝ)) -
                (row f : ℝ) * Real.log ((profileMass row : ℝ) / (M : ℝ)))) +
              (profileMass row : ℝ) * Real.log ((profileMass row : ℝ) / (M : ℝ)) := by
            rw [Finset.sum_congr rfl fun f _ ↦ hterm f]
      _ = ∑ f, -(row f : ℝ) * Real.log ((row f : ℝ) / (profileMass row : ℝ)) := by
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmassSum]
            ring

/-- **The exponential base is the source's `η` product.**  The conditional entropy base attached
to a joint cell/feature profile factors as the product, over compatibility cells, of
`exp(w_c · H(γ_c))`, where `w_c` is the supplied cell mass and `γ_c` is the prescribed law
on that cell.

This is exactly the exponent displayed in `constituent.tex` lines 416--432 of
`papers/2404.16349v3`, and the `η_W^f` of `hyp:quotient-count` in `better_bound/paper.tex`. -/
theorem conditionalProfileEntropyBase_eq_prod_cellBase
    (cellProfile : C → ℕ) (jointProfile : C × F → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = cellProfile) :
    conditionalProfileEntropyBase cellProfile jointProfile =
      ∏ c, Real.exp ((cellProfile c : ℝ) *
        profileEntropyNats fun f ↦ jointProfile (c, f)) := by
  classical
  have hrowMass : ∀ c, profileMass (fun f ↦ jointProfile (c, f)) = cellProfile c := by
    intro c
    have hc := mappedType_fst_apply jointProfile c
    rw [hmargin] at hc
    simp only [profileMass]
    exact hc.symm
  have hjointMass : profileMass jointProfile = profileMass cellProfile := by
    rw [← hmargin]
    exact (profileMass_mappedType Prod.fst jointProfile).symm
  have hle : ∀ c, profileMass (fun f ↦ jointProfile (c, f)) ≤ profileMass cellProfile := by
    intro c
    rw [hrowMass c]
    exact Finset.single_le_sum (f := cellProfile) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c)
  rw [← Real.exp_sum]
  unfold conditionalProfileEntropyBase
  congr 1
  rw [profileMass_mul_profileEntropyNats jointProfile,
    profileMass_mul_profileEntropyNats cellProfile, hjointMass]
  have hjointSplit :
      ∑ x : C × F, -(jointProfile x : ℝ) *
          Real.log ((jointProfile x : ℝ) / (profileMass cellProfile : ℝ)) =
        ∑ c, ∑ f, -(jointProfile (c, f) : ℝ) *
          Real.log ((jointProfile (c, f) : ℝ) / (profileMass cellProfile : ℝ)) :=
    Fintype.sum_prod_type _
  rw [hjointSplit, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have hcell := cell_entropy_term (M := profileMass cellProfile)
    (row := fun f ↦ jointProfile (c, f)) (hle c)
  rw [hrowMass c] at hcell
  have hrhs : (cellProfile c : ℝ) * profileEntropyNats (fun f ↦ jointProfile (c, f)) =
      ∑ f, -(jointProfile (c, f) : ℝ) *
        Real.log ((jointProfile (c, f) : ℝ) / (cellProfile c : ℝ)) := by
    rw [← hrowMass c]
    exact profileMass_mul_profileEntropyNats _
  rw [hrhs, ← hcell]
  ring

end Entropy

/-! ## Sequence-facing form and uniformity over the certificate nodes -/

section Sequence

variable {C : Type u} {F : Type v} [Fintype C] [Fintype F]

/-- Loss-free cellwise count at an exact proportional profile: for a fixed coarse word of the
scaled type, the compatible fine words are counted exactly by the product of the scaled per-cell
multinomial coefficients. -/
theorem card_proportionalConditionalTypeClass_eq_prod_multinomial
    (cellProfile : C → ℕ) (jointProfile : C × F → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = cellProfile) (k : ℕ)
    (source : Fin (profileMass cellProfile * k) → C)
    (hsource : multiplicity source = proportionalCounts cellProfile k) :
    (conditionalTypeClass source (proportionalCounts jointProfile k)).card =
      ∏ c, Nat.multinomial Finset.univ fun f ↦ jointProfile (c, f) * k := by
  have hjointMass : profileMass jointProfile = profileMass cellProfile := by
    rw [← hmargin]
    exact (profileMass_mappedType Prod.fst jointProfile).symm
  have hjoint : proportionalCounts jointProfile k ∈
      types (C × F) (profileMass cellProfile * k) := by
    simpa only [hjointMass] using proportionalCounts_mem_types jointProfile k
  have hmap : mappedType Prod.fst (proportionalCounts jointProfile k) =
      multiplicity source := by
    rw [mappedType_proportionalCounts, hmargin]
    exact hsource.symm
  exact card_conditionalTypeClass_eq_prod_multinomial source _ hjoint hmap

/-- **Claim-6.18 shape for one certificate node.**  The number of compatible fine blocks is at
most a positive subexponential loss times the `k`-th power of the *cell product*
`∏_c exp(w_c · H(γ_c))`. -/
theorem card_proportionalConditionalTypeClass_le_loss_mul_prod_cellBase_pow
    (cellProfile : C → ℕ) (jointProfile : C × F → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile) (k : ℕ) (hk : 0 < k)
    (source : Fin (profileMass cellProfile * k) → C)
    (hsource : multiplicity source = proportionalCounts cellProfile k) :
    ((conditionalTypeClass source (proportionalCounts jointProfile k)).card : ℝ) ≤
      pushedConditionalTypeLoss cellProfile k *
        (∏ c, Real.exp ((cellProfile c : ℝ) *
          profileEntropyNats fun f ↦ jointProfile (c, f))) ^ k := by
  have hbound := card_proportionalConditionalTypeClass_le_loss_mul_entropyBase_pow
    cellProfile jointProfile hmargin hmass k hk source hsource
  rwa [conditionalProfileEntropyBase_eq_prod_cellBase cellProfile jointProfile hmargin] at hbound

end Sequence

section Family

variable {Node : Type w}

/-- **Uniformity over the finitely many certificate nodes.**  A per-node bound
`count ≤ loss × base ^ k` at a fixed repetition `k` upgrades to one bound with the `Finset.sup'`
loss and the `Finset.sup'` base, valid at every node of the family. -/
theorem card_le_sup'_mul_sup'_pow
    (nodes : Finset Node) (hne : nodes.Nonempty)
    (count loss base : Node → ℝ) (k : ℕ)
    (hbase : ∀ node ∈ nodes, 0 ≤ base node)
    (hloss : ∀ node ∈ nodes, 0 ≤ loss node)
    (hcount : ∀ node ∈ nodes, count node ≤ loss node * base node ^ k)
    {node : Node} (hnode : node ∈ nodes) :
    count node ≤ (nodes.sup' hne loss) * (nodes.sup' hne base) ^ k := by
  refine (hcount node hnode).trans ?_
  have hbaseLe : base node ≤ nodes.sup' hne base := Finset.le_sup' base hnode
  have hlossLe : loss node ≤ nodes.sup' hne loss := Finset.le_sup' loss hnode
  have hpow : base node ^ k ≤ (nodes.sup' hne base) ^ k := by
    gcongr
    exact hbase node hnode
  calc
    loss node * base node ^ k ≤ loss node * (nodes.sup' hne base) ^ k :=
      mul_le_mul_of_nonneg_left hpow (hloss node hnode)
    _ ≤ (nodes.sup' hne loss) * (nodes.sup' hne base) ^ k :=
      mul_le_mul_of_nonneg_right hlossLe
        (pow_nonneg (le_trans (hbase node hnode) hbaseLe) k)

/-- The uniform loss appearing in `card_proportionalConditionalTypeClass_le_sup'_loss_mul_sup'_base_pow`
is still subexponential. -/
theorem subexponential_sup'_pushedConditionalTypeLoss [DecidableEq Node]
    {C : Type u} [Fintype C]
    (nodes : Finset Node) (hne : nodes.Nonempty) (cellProfile : Node → C → ℕ) :
    Growth.Subexponential
      (fun k ↦ nodes.sup' hne fun node ↦ pushedConditionalTypeLoss (cellProfile node) k) :=
  Growth.Subexponential.finset_sup' nodes hne _ fun node _ ↦
    pushedConditionalTypeLoss_subexponential (cellProfile node)

/-- **The finite-family Claim-6.18 bound.**  One inequality, with one subexponential loss and one
exponential base, holding at every node of a finite certificate family.  This is the form
consumed when the estimate has to compose through the fixed recursion depth. -/
theorem card_proportionalConditionalTypeClass_le_sup'_loss_mul_sup'_base_pow
    {C : Type u} {F : Type v} [Fintype C] [Fintype F]
    (nodes : Finset Node) (hne : nodes.Nonempty)
    (cellProfile : Node → C → ℕ) (jointProfile : Node → C × F → ℕ)
    (hmargin : ∀ node, mappedType Prod.fst (jointProfile node) = cellProfile node)
    (hmass : ∀ node, 0 < profileMass (cellProfile node))
    (k : ℕ) (hk : 0 < k)
    (source : ∀ node : Node, Fin (profileMass (cellProfile node) * k) → C)
    (hsource : ∀ node, multiplicity (source node) = proportionalCounts (cellProfile node) k)
    {node : Node} (hnode : node ∈ nodes) :
    ((conditionalTypeClass (source node)
        (proportionalCounts (jointProfile node) k)).card : ℝ) ≤
      (nodes.sup' hne fun m ↦ pushedConditionalTypeLoss (cellProfile m) k) *
        (nodes.sup' hne fun m ↦
          ∏ c, Real.exp ((cellProfile m c : ℝ) *
            profileEntropyNats fun f ↦ jointProfile m (c, f))) ^ k := by
  refine card_le_sup'_mul_sup'_pow nodes hne
    (count := fun m ↦ ((conditionalTypeClass (source m)
      (proportionalCounts (jointProfile m) k)).card : ℝ))
    (loss := fun m ↦ pushedConditionalTypeLoss (cellProfile m) k)
    (base := fun m ↦ ∏ c, Real.exp ((cellProfile m c : ℝ) *
      profileEntropyNats fun f ↦ jointProfile m (c, f)))
    k ?_ ?_ ?_ hnode
  · intro m _
    exact Finset.prod_nonneg fun c _ ↦ (Real.exp_pos _).le
  · intro m _
    exact (pushedConditionalTypeLoss_pos (cellProfile m) k).le
  · intro m _
    exact card_proportionalConditionalTypeClass_le_loss_mul_prod_cellBase_pow
      (cellProfile m) (jointProfile m) (hmargin m) (hmass m) k hk (source m) (hsource m)

end Family

end WordType

end AlgebraicComplexity
