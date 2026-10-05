/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.BinomialEntropyEnvelope
import AlgebraicComplexity.Analysis.ProportionalMultinomial
import AlgebraicComplexity.Examples.CoppersmithWinogradFirstPowerHashing

/-!
# The rectangular multiplicity type for the full Coppersmith--Winograd tensor

`Examples/CoppersmithWinogradFirstPowerHashing.lean` runs the laser pipeline for the
six-constituent tensor `CW_q` of [CW90, Eq. (10)] at the *single* rational type
`(10481, 19038, 481)/30000`, and ends at `cwFirstPower_base_inequality`, the scalar inequality
behind `ω < 2.3872`.  Huang and Pan [HP98, Sections 5 and 7.1] run the very same pipeline at a
*two-parameter family* of types and read a rectangular bound off it, culminating in
`ω(1,1,2) < 3.334`.  This module is the type layer of that family.

## Huang--Pan's block shape

In the `(2+r)N`-th tensor power of `CW_q` they set (verbatim, [HP98, p. 275]) `x^{[I]} = 0` unless
`I` has exactly `r(N-L) + 2L` indices `0`, exactly `2(N-L)` indices `1` and exactly `rL` indices
`2`, and similarly for `y` and `z` with `(N + rL, (1+r)(N-L), L)`.  What survives is the list on
[HP98, p. 276]: among the `(2+r)N` copies of the base algorithm one picks

```text
x^{[0]}_0 y^{[1]}_i z^{[1]}_i   from  r(N-L) copies      (block address cw011)
x^{[1]}_i y^{[0]}_0 z^{[1]}_i   from   (N-L) copies      (block address cw101)
x^{[1]}_i y^{[1]}_i z^{[0]}_0   from   (N-L) copies      (block address cw110)
x^{[0]}_0 y^{[0]}_0 z^{[2]}_{q+1}   from     L copies    (block address cw002)
x^{[0]}_0 y^{[2]}_{q+1} z^{[0]}_0   from     L copies    (block address cw020)
x^{[2]}_{q+1} y^{[0]}_0 z^{[0]}_0   from    rL copies    (block address cw200)
```

so the Huang--Pan type is, in the block-address language of this repository, the *denominator-free*
profile

```text
cwRectType a b e f :  cw011 ↦ a,  cw101 ↦ b,  cw110 ↦ b,  cw002 ↦ e,  cw020 ↦ e,  cw200 ↦ f
```

with `a = r(N-L)`, `b = N-L`, `e = L`, `f = rL`.  Nothing in this module assumes the Huang--Pan
relation `a/b = f/e = r`; it is only their (optimal) choice, and the theorems below hold for every
`(a, b, e, f)`.

The constituent dimensions of `CW_q` are `⟨1,1,q⟩` at `cw011`, `⟨q,1,1⟩` at `cw101`, `⟨1,q,1⟩` at
`cw110` and `⟨1,1,1⟩` at the three corners, so the surviving block product is
`⟨q^b, q^b, q^a⟩` (`cwRect_positiveWordProduct_m/n/p`), which is `⟨n, n, n^r⟩` for `n = q^b`,
matching [HP98, p. 276] exactly.  The `β = 0` degenerate case `e = f = 0` is Section 6 of the same
paper and is already covered by the *easy*-tensor modules
`Examples/CoppersmithWinogradEasyRectangular*.lean`; the corner blocks are exactly what upgrades
`(6.1)` to `(7.1)`.

## Main definitions and results

* `cwRectAddressCount` / `cwRectType` -- the profile above;
* `cwRectDepth`, `cwRectTypeWords`, `card_cwRectTypeWords` -- the word family and its exact
  six-fold multinomial cardinality, which is [HP98]'s
  `((2+r)N; L, L, rL, r(N-L), N-L, N-L)`;
* `cwRect_positiveWordProduct_m/n/p` -- the dimension formulas `q^b, q^b, q^a`, at an arbitrary
  depth so that they specialize definitionally at `r = 1`;
* `cwRectMarginalType`, `cwRect_mappedType_eq`, `cwRectType_unique_of_mappedTypes` -- the three
  leg marginals and the fact that they determine the joint type, which is what makes the leg-local
  selection of the hashing stage exact;
* `cwRectLegTypedFiber`, `card_cwRectTypedWordMapFiber` -- the *type-restricted* leg fiber, whose
  exact size is Huang--Pan's competitor count: `((r(N-L)+2L); r(N-L), L, L)·((2(N-L)); N-L, N-L)`
  on the `x` leg and `((N+rL); N-L, L, rL)·(((1+r)(N-L)); N-L, r(N-L))` on the other two;
* `cwRectLegTypedFiber_X_le_Y` -- for `b ≤ a`, `2e ≤ b` and `e ≤ f` (which contains Huang--Pan's
  regime `r ≥ 1`, `β ≤ 1/3`) the maximum over legs is attained on the `y` and `z` legs.  This is
  their sentence "we select the larger former bound"; the opposite regime is their (7.2);
* `proportionalEntropyBase_cwRectType`, `cwRectType_entropyBase_pow_le_loss_mul_card` -- the
  method-of-types (Stirling) estimate of [HP98, p. 277];
* `cwRectType_firstPower` and the `*_firstPower` regressions -- **at `(a,b,e,f) = (9519k, 9519k,
  481k, 481k)` this module's type *is* `cwFirstPowerNaturalType k`**, so `r = 1`, `β = 0.0481`
  reproduces the existing `ω < 2.3872` client exactly.

## References

* [CW90] D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic progressions*,
  J. Symbolic Comput. **9** (1990), 251--280; Eq. (10) and Section 7.
* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299; Section 5 (pp. 269--271) and Section 7.1
  (pp. 275--277).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-! ## The rectangular multiplicity profile -/

/-- Huang--Pan's rectangular multiplicity profile on the ambient CW block addresses.

The two "middle" addresses that carry a `q`-dimensional leg on `y` and `z` get `b`, the one that
carries it on `x` gets `a`, the two corners whose distinguished leg is `y` or `z` get `e`, and the
corner distinguished on `x` gets `f`.  With `(a, b, e, f) = (r(N-L), N-L, L, rL)` this is exactly
the [HP98, p. 276] zeroing pattern. -/
def cwRectAddressCount (a b e f : ℕ) (s : CWBlockAddress) : ℕ :=
  match s .X, s .Y, s .Z with
  | .last, .zero, .zero => f
  | .zero, .last, .zero => e
  | .zero, .zero, .last => e
  | .zero, .middle, .middle => a
  | .middle, .zero, .middle => b
  | _, _, _ => b

@[simp] theorem cwRectAddressCount_cw200 (a b e f : ℕ) :
    cwRectAddressCount a b e f cw200 = f := rfl

@[simp] theorem cwRectAddressCount_cw020 (a b e f : ℕ) :
    cwRectAddressCount a b e f cw020 = e := rfl

@[simp] theorem cwRectAddressCount_cw002 (a b e f : ℕ) :
    cwRectAddressCount a b e f cw002 = e := rfl

@[simp] theorem cwRectAddressCount_cw011 (a b e f : ℕ) :
    cwRectAddressCount a b e f cw011 = a := rfl

@[simp] theorem cwRectAddressCount_cw101 (a b e f : ℕ) :
    cwRectAddressCount a b e f cw101 = b := rfl

@[simp] theorem cwRectAddressCount_cw110 (a b e f : ℕ) :
    cwRectAddressCount a b e f cw110 = b := rfl

/-- The rectangular multiplicity type on the six supported CW constituents. -/
def cwRectType (a b e f : ℕ) : cwBlockSupport → ℕ :=
  fun s ↦ cwRectAddressCount a b e f s.1

@[simp] theorem cwRectType_apply (a b e f : ℕ) (s : cwBlockSupport) :
    cwRectType a b e f s = cwRectAddressCount a b e f s.1 := rfl

theorem cwRectType_pos {a b e f : ℕ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e) (hf : 0 < f)
    (s : cwBlockSupport) : 0 < cwRectType a b e f s := by
  unfold cwRectType cwRectAddressCount
  split <;> assumption

/-- Total mass of the rectangular profile: the tensor power has `a + 2b + 2e + f` factors.  With
Huang--Pan's parameters this is `(2+r)N`. -/
@[simp] theorem sum_cwRectType (a b e f : ℕ) :
    ∑ s : cwBlockSupport, cwRectType a b e f s = a + 2 * b + 2 * e + f := by
  have h : (∑ s : cwBlockSupport, cwRectType a b e f s) =
      ∑ s ∈ cwBlockSupport, cwRectAddressCount a b e f s :=
    (Finset.sum_subtype cwBlockSupport (fun _ ↦ Iff.rfl) (cwRectAddressCount a b e f)).symm
  rw [h, sum_cwBlockSupport, cwRectAddressCount_cw200, cwRectAddressCount_cw020,
    cwRectAddressCount_cw002, cwRectAddressCount_cw011, cwRectAddressCount_cw101,
    cwRectAddressCount_cw110]
  ring

/-- Positive-word depth representing a tensor power with `a + 2b + 2e + f` factors. -/
def cwRectDepth (a b e f : ℕ) : ℕ := a + 2 * b + 2 * e + f - 1

theorem cwRectDepth_add_one {a b e f : ℕ} (h : 0 < a + 2 * b + 2 * e + f) :
    cwRectDepth a b e f + 1 = a + 2 * b + 2 * e + f := by
  unfold cwRectDepth
  omega

theorem cwRectType_mem_types {a b e f : ℕ} (h : 0 < a + 2 * b + 2 * e + f) :
    cwRectType a b e f ∈ WordType.types cwBlockSupport (cwRectDepth a b e f + 1) := by
  rw [WordType.mem_types, sum_cwRectType, cwRectDepth_add_one h]

/-- Rectangular-type supported-address words in the `(a + 2b + 2e + f)`-fold CW tensor power. -/
noncomputable def cwRectTypeWords (a b e f : ℕ) :
    Finset (PositiveWord cwBlockSupport (cwRectDepth a b e f)) :=
  positiveTypeClass cwBlockSupport (cwRectDepth a b e f) (cwRectType a b e f)

/-- Exact six-fold multinomial size of the rectangular word family.  This is Huang--Pan's
`((2+r)N; L, L, rL, r(N-L), N-L, N-L)` of [HP98, p. 276]. -/
theorem card_cwRectTypeWords {a b e f : ℕ} (h : 0 < a + 2 * b + 2 * e + f) :
    (cwRectTypeWords a b e f).card = Nat.multinomial Finset.univ (cwRectType a b e f) :=
  card_positiveTypeClass_eq_multinomial _ _ (cwRectType_mem_types h)

theorem cwRectTypeWords_nonempty {a b e f : ℕ} (h : 0 < a + 2 * b + 2 * e + f) :
    (cwRectTypeWords a b e f).Nonempty := by
  rw [← Finset.card_pos, card_cwRectTypeWords h]
  exact Nat.multinomial_pos _ _

/-! ## The rectangular dimension formulas -/

/-- In a rectangular-type word the first matrix-multiplication dimension multiplies to `q^b`. -/
theorem cwRect_positiveWordProduct_m (K : Type u) [CommRing K] (q a b e f d : ℕ)
    {word : PositiveWord (cwPartitionedTensor K q).support d}
    (hword : word ∈ positiveTypeClass (cwPartitionedTensor K q).support d
      (cwRectType a b e f)) :
    positiveWordProduct (cwTensorConstituentM K q) d word = q ^ b := by
  classical
  rw [positiveWordProduct_eq_prod_pow (a := cwRectType a b e f)
    (cwTensorConstituentM K q) hword]
  change (∏ s : cwBlockSupport,
    (cwConstituentDimensions q s.1).1 ^ cwRectAddressCount a b e f s.1) = q ^ b
  calc
    (∏ s : cwBlockSupport,
        (cwConstituentDimensions q s.1).1 ^ cwRectAddressCount a b e f s.1) =
        ∏ s ∈ cwBlockSupport,
          (cwConstituentDimensions q s).1 ^ cwRectAddressCount a b e f s :=
      (Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).1 ^ cwRectAddressCount a b e f s)).symm
    _ = q ^ b := by
      rw [prod_cwBlockSupport]
      simp

/-- In a rectangular-type word the second matrix-multiplication dimension multiplies to `q^b`. -/
theorem cwRect_positiveWordProduct_n (K : Type u) [CommRing K] (q a b e f d : ℕ)
    {word : PositiveWord (cwPartitionedTensor K q).support d}
    (hword : word ∈ positiveTypeClass (cwPartitionedTensor K q).support d
      (cwRectType a b e f)) :
    positiveWordProduct (cwTensorConstituentN K q) d word = q ^ b := by
  classical
  rw [positiveWordProduct_eq_prod_pow (a := cwRectType a b e f)
    (cwTensorConstituentN K q) hword]
  change (∏ s : cwBlockSupport,
    (cwConstituentDimensions q s.1).2.1 ^ cwRectAddressCount a b e f s.1) = q ^ b
  calc
    (∏ s : cwBlockSupport,
        (cwConstituentDimensions q s.1).2.1 ^ cwRectAddressCount a b e f s.1) =
        ∏ s ∈ cwBlockSupport,
          (cwConstituentDimensions q s).2.1 ^ cwRectAddressCount a b e f s :=
      (Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).2.1 ^ cwRectAddressCount a b e f s)).symm
    _ = q ^ b := by
      rw [prod_cwBlockSupport]
      simp

/-- In a rectangular-type word the third matrix-multiplication dimension multiplies to `q^a`.
This is the stretched leg: with `a = r·b` the block product is `⟨n, n, n^r⟩` for `n = q^b`. -/
theorem cwRect_positiveWordProduct_p (K : Type u) [CommRing K] (q a b e f d : ℕ)
    {word : PositiveWord (cwPartitionedTensor K q).support d}
    (hword : word ∈ positiveTypeClass (cwPartitionedTensor K q).support d
      (cwRectType a b e f)) :
    positiveWordProduct (cwTensorConstituentP K q) d word = q ^ a := by
  classical
  rw [positiveWordProduct_eq_prod_pow (a := cwRectType a b e f)
    (cwTensorConstituentP K q) hword]
  change (∏ s : cwBlockSupport,
    (cwConstituentDimensions q s.1).2.2 ^ cwRectAddressCount a b e f s.1) = q ^ a
  calc
    (∏ s : cwBlockSupport,
        (cwConstituentDimensions q s.1).2.2 ^ cwRectAddressCount a b e f s.1) =
        ∏ s ∈ cwBlockSupport,
          (cwConstituentDimensions q s).2.2 ^ cwRectAddressCount a b e f s :=
      (Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).2.2 ^ cwRectAddressCount a b e f s)).symm
    _ = q ^ a := by
      rw [prod_cwBlockSupport]
      simp

/-! ## The three leg marginals -/

/-- The pushforward of the rectangular profile along the leg-`c` projection.

Reading [HP98, p. 275]: the `x` leg has `r(N-L) + 2L` zeros, `2(N-L)` middles and `rL` lasts; the
`y` and `z` legs have `N + rL` zeros, `(1+r)(N-L)` middles and `L` lasts. -/
def cwRectMarginalType (a b e f : ℕ) : Leg → CWBlock → ℕ
  | .X, .zero => a + 2 * e
  | .X, .middle => 2 * b
  | .X, .last => f
  | .Y, .zero => b + e + f
  | .Y, .middle => a + b
  | .Y, .last => e
  | .Z, .zero => b + e + f
  | .Z, .middle => a + b
  | .Z, .last => e

/-- The leg-`c` marginal of the rectangular profile really is `cwRectMarginalType`. -/
theorem cwRect_mappedType_eq (a b e f : ℕ) (c : Leg) :
    WordType.mappedType (fun s : cwBlockSupport ↦ s.1 c) (cwRectType a b e f) =
      cwRectMarginalType a b e f c := by
  funext β
  rw [cw_mappedType_eq_naturalMarginal]
  cases c <;> cases β <;>
    simp only [cwNaturalMarginal, cwRectMarginalType, cwRectType,
      cwRectAddressCount_cw200, cwRectAddressCount_cw020,
      cwRectAddressCount_cw002, cwRectAddressCount_cw011, cwRectAddressCount_cw101,
      cwRectAddressCount_cw110] <;> omega

/-- Total mass of a leg marginal is the total mass of the profile. -/
@[simp] theorem sum_cwRectMarginalType (a b e f : ℕ) (c : Leg) :
    ∑ β : CWBlock, cwRectMarginalType a b e f c β = a + 2 * b + 2 * e + f := by
  rw [← cwRect_mappedType_eq a b e f c, WordType.sum_mappedType, sum_cwRectType]

theorem cwRectMarginalType_mem_types {a b e f : ℕ} (h : 0 < a + 2 * b + 2 * e + f) (c : Leg) :
    cwRectMarginalType a b e f c ∈ WordType.types CWBlock (cwRectDepth a b e f + 1) := by
  rw [WordType.mem_types, sum_cwRectMarginalType, cwRectDepth_add_one h]

/-- **The three leg marginals determine the joint type.**  This is what makes the leg-local
selection of the hashing stage an exact description of the rectangular type class: reading `f` off
the `x` last-count, `e` off the `y` and `z` last-counts, and then solving the three middle-count
equations `cw101 + cw110 = 2b`, `cw011 + cw110 = a + b`, `cw011 + cw101 = a + b`. -/
theorem cwRectType_unique_of_mappedTypes (a b e f : ℕ) (g : cwBlockSupport → ℕ)
    (h : ∀ c, WordType.mappedType (fun s : cwBlockSupport ↦ s.1 c) g =
      cwRectMarginalType a b e f c) :
    g = cwRectType a b e f := by
  have hXlast := congrFun (h .X) .last
  have hYlast := congrFun (h .Y) .last
  have hZlast := congrFun (h .Z) .last
  have hXmiddle := congrFun (h .X) .middle
  have hYmiddle := congrFun (h .Y) .middle
  have hZmiddle := congrFun (h .Z) .middle
  rw [cw_mappedType_eq_naturalMarginal] at hXlast hYlast hZlast
  rw [cw_mappedType_eq_naturalMarginal] at hXmiddle hYmiddle hZmiddle
  simp only [cwNaturalMarginal, cwRectMarginalType] at hXlast hYlast hZlast
  simp only [cwNaturalMarginal, cwRectMarginalType] at hXmiddle hYmiddle hZmiddle
  funext s
  rcases s with ⟨s, hs⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · change g cw200S = f
    exact hXlast
  · change g cw020S = e
    exact hYlast
  · change g cw002S = e
    exact hZlast
  · change g cw011S = a
    omega
  · change g cw101S = b
    omega
  · show g cw110S = b
    omega

/-- The multiplicity type of a leg word of a rectangular-type source word is the leg marginal. -/
theorem cwRectLegWord_multiplicity (a b e f d : ℕ)
    (w : PositiveWord cwBlockSupport d)
    (hw : w ∈ positiveTypeClass cwBlockSupport d (cwRectType a b e f)) (c : Leg) :
    WordType.multiplicity
        (positiveWordEquiv CWBlock d
          (PartitionHashEncoding.supportWordAddress
            (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) d w c)) =
      cwRectMarginalType a b e f c := by
  rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
    (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) d w c]
  change WordType.multiplicity
    ((fun s : cwBlockSupport ↦ s.1 c) ∘ positiveWordEquiv cwBlockSupport d w) = _
  rw [WordType.multiplicity_comp_eq_mappedType, mem_positiveTypeClass.mp hw,
    cwRect_mappedType_eq]

/-! ## The type-restricted leg fiber

Huang--Pan's competitor list `M` is the set of lifts of a leg word that still carry the selected
*joint* type, i.e. `WordType.typedWordMapFiber`.  Its exact size is computed here by the
division-free double counting `WordType.card_targetType_mul_card_typedWordMapFiber`. -/

/-- Huang--Pan's exact competitor count on leg `c` ([HP98, p. 276]):
`((r(N-L)+2L); r(N-L), L, L)·((2(N-L)); N-L, N-L)` on the `x` leg and
`((N+rL); N-L, L, rL)·(((1+r)(N-L)); N-L, r(N-L))` on the `y` and `z` legs. -/
def cwRectLegTypedFiber (a b e f : ℕ) : Leg → ℕ
  | .X => Nat.choose (a + 2 * e) a * Nat.choose (2 * e) e * Nat.choose (2 * b) b
  | .Y => Nat.choose (b + e + f) b * Nat.choose (e + f) e * Nat.choose (a + b) a
  | .Z => Nat.choose (b + e + f) b * Nat.choose (e + f) e * Nat.choose (a + b) a

theorem cwRectLegTypedFiber_pos (a b e f : ℕ) (c : Leg) : 0 < cwRectLegTypedFiber a b e f c := by
  cases c <;>
    exact Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
      (Nat.choose_pos (by omega))

/-- Factorial product of the rectangular profile. -/
theorem prod_factorial_cwRectType (a b e f : ℕ) :
    (∏ s : cwBlockSupport, (cwRectType a b e f s).factorial) =
      f.factorial * (e.factorial * (e.factorial *
        (a.factorial * (b.factorial * b.factorial)))) := by
  have h : (∏ s : cwBlockSupport, (cwRectType a b e f s).factorial) =
      ∏ s ∈ cwBlockSupport, (cwRectAddressCount a b e f s).factorial :=
    (Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
      (fun s ↦ (cwRectAddressCount a b e f s).factorial)).symm
  rw [h, prod_cwBlockSupport, cwRectAddressCount_cw200, cwRectAddressCount_cw020,
    cwRectAddressCount_cw002, cwRectAddressCount_cw011, cwRectAddressCount_cw101,
    cwRectAddressCount_cw110]

/-- Factorial product of a leg marginal profile. -/
theorem prod_factorial_cwRectMarginalType (a b e f : ℕ) (c : Leg) :
    (∏ β : CWBlock, (cwRectMarginalType a b e f c β).factorial) =
      (cwRectMarginalType a b e f c .zero).factorial *
        (cwRectMarginalType a b e f c .middle).factorial *
        (cwRectMarginalType a b e f c .last).factorial := by
  rw [show (Finset.univ : Finset CWBlock) = {CWBlock.zero, CWBlock.middle, CWBlock.last} by decide]
  simp [mul_assoc]

/-- The factorial identity behind the typed fiber count: dividing the marginal factorial product
by the joint one leaves exactly `cwRectLegTypedFiber`. -/
theorem factorial_cwRectMarginal_eq (a b e f : ℕ) (c : Leg) :
    (cwRectMarginalType a b e f c .zero).factorial *
        (cwRectMarginalType a b e f c .middle).factorial *
        (cwRectMarginalType a b e f c .last).factorial =
      f.factorial * (e.factorial * (e.factorial *
        (a.factorial * (b.factorial * b.factorial)))) * cwRectLegTypedFiber a b e f c := by
  have hae :
      Nat.choose (a + 2 * e) a * a.factorial * (2 * e).factorial = (a + 2 * e).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + 2 * e by omega)
    rwa [show a + 2 * e - a = 2 * e from by omega] at h
  have hee : Nat.choose (2 * e) e * e.factorial * e.factorial = (2 * e).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show e ≤ 2 * e by omega)
    rwa [show 2 * e - e = e from by omega] at h
  have hbb : Nat.choose (2 * b) b * b.factorial * b.factorial = (2 * b).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show b ≤ 2 * b by omega)
    rwa [show 2 * b - b = b from by omega] at h
  have hbef : Nat.choose (b + e + f) b * b.factorial * (e + f).factorial =
      (b + e + f).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show b ≤ b + e + f by omega)
    rwa [show b + e + f - b = e + f from by omega] at h
  have hef : Nat.choose (e + f) e * e.factorial * f.factorial = (e + f).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show e ≤ e + f by omega)
    rwa [show e + f - e = f from by omega] at h
  have hab : Nat.choose (a + b) a * a.factorial * b.factorial = (a + b).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    rwa [show a + b - a = b from by omega] at h
  cases c with
  | X =>
      simp only [cwRectMarginalType, cwRectLegTypedFiber]
      rw [← hae, ← hee, ← hbb]
      ring
  | Y =>
      simp only [cwRectMarginalType, cwRectLegTypedFiber]
      rw [← hbef, ← hef, ← hab]
      ring
  | Z =>
      simp only [cwRectMarginalType, cwRectLegTypedFiber]
      rw [← hbef, ← hef, ← hab]
      ring

/-- The joint rectangular multinomial factors as the leg marginal multinomial times
`cwRectLegTypedFiber`.  Division-free form of `joint / marginal`. -/
theorem multinomial_cwRectType_eq (a b e f : ℕ) (c : Leg) :
    Nat.multinomial (Finset.univ : Finset cwBlockSupport) (cwRectType a b e f) =
      cwRectLegTypedFiber a b e f c *
        Nat.multinomial (Finset.univ : Finset CWBlock) (cwRectMarginalType a b e f c) := by
  have h1 := Nat.multinomial_spec (Finset.univ : Finset cwBlockSupport) (cwRectType a b e f)
  have h2 := Nat.multinomial_spec (Finset.univ : Finset CWBlock)
    (cwRectMarginalType a b e f c)
  rw [prod_factorial_cwRectType, sum_cwRectType] at h1
  rw [prod_factorial_cwRectMarginalType, sum_cwRectMarginalType,
    factorial_cwRectMarginal_eq] at h2
  set P : ℕ := f.factorial * (e.factorial * (e.factorial *
    (a.factorial * (b.factorial * b.factorial)))) with hP
  have hpos : 0 < P := by
    rw [hP]
    exact Nat.mul_pos (Nat.factorial_pos f) (Nat.mul_pos (Nat.factorial_pos e)
      (Nat.mul_pos (Nat.factorial_pos e) (Nat.mul_pos (Nat.factorial_pos a)
        (Nat.mul_pos (Nat.factorial_pos b) (Nat.factorial_pos b)))))
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc P * Nat.multinomial (Finset.univ : Finset cwBlockSupport) (cwRectType a b e f)
      = (a + 2 * b + 2 * e + f).factorial := h1
    _ = P * cwRectLegTypedFiber a b e f c *
        Nat.multinomial (Finset.univ : Finset CWBlock)
          (cwRectMarginalType a b e f c) := h2.symm
    _ = P * (cwRectLegTypedFiber a b e f c *
        Nat.multinomial (Finset.univ : Finset CWBlock)
          (cwRectMarginalType a b e f c)) := by ring

/-- **Exact type-restricted leg fiber.**  Among the lifts of a leg word of the rectangular
marginal type, exactly `cwRectLegTypedFiber a b e f c` again have the joint type. -/
theorem card_cwRectTypedWordMapFiber {a b e f d : ℕ} (hd : d + 1 = a + 2 * b + 2 * e + f)
    (c : Leg) (target : Fin (d + 1) → CWBlock)
    (htarget : WordType.multiplicity target = cwRectMarginalType a b e f c) :
    (WordType.typedWordMapFiber (fun s : cwBlockSupport ↦ s.1 c) (cwRectType a b e f)
        target).card = cwRectLegTypedFiber a b e f c := by
  classical
  have hdouble := WordType.card_targetType_mul_card_typedWordMapFiber
    (fun s : cwBlockSupport ↦ s.1 c) (cwRectType a b e f) target
    (by rw [WordType.mem_typeClass, htarget, cwRect_mappedType_eq])
  rw [cwRect_mappedType_eq] at hdouble
  have hmarg : (WordType.typeClass (d + 1) (cwRectMarginalType a b e f c)).card =
      Nat.multinomial Finset.univ (cwRectMarginalType a b e f c) :=
    WordType.card_typeClass_eq_multinomial _
      (by rw [WordType.mem_types, sum_cwRectMarginalType, hd])
  have hrect : (WordType.typeClass (d + 1) (cwRectType a b e f)).card =
      Nat.multinomial Finset.univ (cwRectType a b e f) :=
    WordType.card_typeClass_eq_multinomial _
      (by rw [WordType.mem_types, sum_cwRectType, hd])
  rw [hmarg, hrect, multinomial_cwRectType_eq a b e f c] at hdouble
  refine Nat.eq_of_mul_eq_mul_left
    (Nat.multinomial_pos (Finset.univ : Finset CWBlock) (cwRectMarginalType a b e f c)) ?_
  rw [hdouble, Nat.mul_comm]

/-! ## Which leg carries the largest fiber

Huang--Pan compare the two counts and "select the larger former bound"; the sign of the comparison
is what separates their (7.1) from their (7.2).  The comparison is a Schur-type factorial
inequality, `Analysis.factorial_mul_factorial_le_of_le` applied twice. -/

/-- The `x`-leg marginal factorial product is at most the `y`-leg one when `b ≤ a`, `2e ≤ b` and
`e ≤ f`.  With Huang--Pan's `a = rb`, `f = re` this is exactly `r ≥ 1` together with `β ≤ 1/3`. -/
theorem cwRect_marginalFactorial_X_le_Y {a b e f : ℕ} (hba : b ≤ a) (heb : 2 * e ≤ b)
    (hef : e ≤ f) :
    (a + 2 * e).factorial * (2 * b).factorial * f.factorial ≤
      (b + e + f).factorial * (a + b).factorial * e.factorial := by
  -- Step 1: move the gap `a - b` from the `x` zero-count onto the `y` middle-count.
  have h1 : (a + 2 * e).factorial * (2 * b).factorial ≤
      (a + b).factorial * (b + 2 * e).factorial := by
    have h := Analysis.factorial_mul_factorial_le_of_le
      (x := b + 2 * e) (y := 2 * b) (d := a - b) (by omega)
    rwa [show b + 2 * e + (a - b) = a + 2 * e from by omega,
      show 2 * b + (a - b) = a + b from by omega] at h
  -- Step 2: move the gap `f - e` from the `x` last-count onto the `y` zero-count.
  have h2 : (b + 2 * e).factorial * f.factorial ≤ (b + e + f).factorial * e.factorial := by
    have h := Analysis.factorial_mul_factorial_le_of_le
      (x := e) (y := b + 2 * e) (d := f - e) (by omega)
    rw [show e + (f - e) = f from by omega,
      show b + 2 * e + (f - e) = b + e + f from by omega] at h
    calc (b + 2 * e).factorial * f.factorial = f.factorial * (b + 2 * e).factorial :=
          Nat.mul_comm _ _
      _ ≤ (b + e + f).factorial * e.factorial := h
  calc (a + 2 * e).factorial * (2 * b).factorial * f.factorial
      ≤ (a + b).factorial * (b + 2 * e).factorial * f.factorial :=
        Nat.mul_le_mul_right _ h1
    _ = (a + b).factorial * ((b + 2 * e).factorial * f.factorial) := by ring
    _ ≤ (a + b).factorial * ((b + e + f).factorial * e.factorial) :=
        Nat.mul_le_mul_left _ h2
    _ = (b + e + f).factorial * (a + b).factorial * e.factorial := by ring

/-- Consequently the `y`-leg marginal type class is the *smallest* of the three. -/
theorem multinomial_cwRectMarginalType_Y_le_X {a b e f : ℕ} (hba : b ≤ a) (heb : 2 * e ≤ b)
    (hef : e ≤ f) :
    Nat.multinomial (Finset.univ : Finset CWBlock) (cwRectMarginalType a b e f .Y) ≤
      Nat.multinomial (Finset.univ : Finset CWBlock) (cwRectMarginalType a b e f .X) := by
  set MX : ℕ := Nat.multinomial (Finset.univ : Finset CWBlock)
    (cwRectMarginalType a b e f .X) with hMX
  set MY : ℕ := Nat.multinomial (Finset.univ : Finset CWBlock)
    (cwRectMarginalType a b e f .Y) with hMY
  have hX : (a + 2 * e).factorial * (2 * b).factorial * f.factorial * MX =
      (a + 2 * b + 2 * e + f).factorial := by
    have h := Nat.multinomial_spec (Finset.univ : Finset CWBlock)
      (cwRectMarginalType a b e f .X)
    rwa [prod_factorial_cwRectMarginalType, sum_cwRectMarginalType] at h
  have hY : (b + e + f).factorial * (a + b).factorial * e.factorial * MY =
      (a + 2 * b + 2 * e + f).factorial := by
    have h := Nat.multinomial_spec (Finset.univ : Finset CWBlock)
      (cwRectMarginalType a b e f .Y)
    rwa [prod_factorial_cwRectMarginalType, sum_cwRectMarginalType] at h
  have hfac := cwRect_marginalFactorial_X_le_Y hba heb hef
  have hFYpos : 0 < (b + e + f).factorial * (a + b).factorial * e.factorial :=
    Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)
  have hchain : (b + e + f).factorial * (a + b).factorial * e.factorial * MY ≤
      (b + e + f).factorial * (a + b).factorial * e.factorial * MX := by
    calc (b + e + f).factorial * (a + b).factorial * e.factorial * MY
        = (a + 2 * b + 2 * e + f).factorial := hY
      _ = (a + 2 * e).factorial * (2 * b).factorial * f.factorial * MX := hX.symm
      _ ≤ (b + e + f).factorial * (a + b).factorial * e.factorial * MX :=
          Nat.mul_le_mul_right _ hfac
  exact Nat.le_of_mul_le_mul_left hchain hFYpos

/-- **The `y` and `z` legs carry the largest type-restricted fiber** when `b ≤ a`, `2e ≤ b` and
`e ≤ f`.  This is Huang--Pan's "we select the larger former bound" [HP98, p. 276]. -/
theorem cwRectLegTypedFiber_X_le_Y {a b e f : ℕ} (hba : b ≤ a) (heb : 2 * e ≤ b) (hef : e ≤ f) :
    cwRectLegTypedFiber a b e f .X ≤ cwRectLegTypedFiber a b e f .Y := by
  have hX := multinomial_cwRectType_eq a b e f .X
  have hY := multinomial_cwRectType_eq a b e f .Y
  have hcomp := multinomial_cwRectMarginalType_Y_le_X hba heb hef
  have hXpos : 0 < Nat.multinomial (Finset.univ : Finset CWBlock)
      (cwRectMarginalType a b e f .X) := Nat.multinomial_pos _ _
  have hkey : cwRectLegTypedFiber a b e f .X *
      Nat.multinomial (Finset.univ : Finset CWBlock) (cwRectMarginalType a b e f .X) ≤
        cwRectLegTypedFiber a b e f .Y *
          Nat.multinomial (Finset.univ : Finset CWBlock)
            (cwRectMarginalType a b e f .X) := by
    calc cwRectLegTypedFiber a b e f .X *
          Nat.multinomial (Finset.univ : Finset CWBlock) (cwRectMarginalType a b e f .X)
        = Nat.multinomial (Finset.univ : Finset cwBlockSupport) (cwRectType a b e f) := hX.symm
      _ = cwRectLegTypedFiber a b e f .Y *
          Nat.multinomial (Finset.univ : Finset CWBlock)
            (cwRectMarginalType a b e f .Y) := hY
      _ ≤ cwRectLegTypedFiber a b e f .Y *
          Nat.multinomial (Finset.univ : Finset CWBlock)
            (cwRectMarginalType a b e f .X) := Nat.mul_le_mul_left _ hcomp
  exact Nat.le_of_mul_le_mul_right hkey hXpos

@[simp] theorem cwRectLegTypedFiber_Z_eq_Y (a b e f : ℕ) :
    cwRectLegTypedFiber a b e f .Z = cwRectLegTypedFiber a b e f .Y := rfl

/-- Under the Huang--Pan hypotheses the `y`-leg fiber dominates all three legs. -/
theorem cwRectLegTypedFiber_le_Y {a b e f : ℕ} (hba : b ≤ a) (heb : 2 * e ≤ b) (hef : e ≤ f)
    (c : Leg) : cwRectLegTypedFiber a b e f c ≤ cwRectLegTypedFiber a b e f .Y := by
  cases c
  · exact cwRectLegTypedFiber_X_le_Y hba heb hef
  · exact le_rfl
  · exact le_rfl

/-! ### The reversed comparison, `r ≤ 1`

For `0 ≤ r ≤ 1` Huang--Pan's two counts compare the other way ([HP98, Section 7.2, p. 277]:
"the small difference is that now `…<…`"), and the `x` leg is the one that is selected.  The proof
is the same two applications of `Analysis.factorial_mul_factorial_le_of_le`, run in the opposite
direction: the gap `b - a` now moves off the `y` middle-count and the gap `e - f` off the `y`
zero-count. -/

/-- The `y`-leg marginal factorial product is at most the `x`-leg one when `a ≤ b`, `2e ≤ b` and
`f ≤ e`.  With Huang--Pan's `a = rb`, `f = re` this is exactly `r ≤ 1` together with
`β ≤ 1/3`. -/
theorem cwRect_marginalFactorial_Y_le_X {a b e f : ℕ} (hab : a ≤ b) (heb : 2 * e ≤ b)
    (hfe : f ≤ e) :
    (b + e + f).factorial * (a + b).factorial * e.factorial ≤
      (a + 2 * e).factorial * (2 * b).factorial * f.factorial := by
  -- Step 1: move the gap `b - a` from the `y` middle-count onto the `x` zero-count.
  have h1 : (b + 2 * e).factorial * (a + b).factorial ≤
      (2 * b).factorial * (a + 2 * e).factorial := by
    have h := Analysis.factorial_mul_factorial_le_of_le
      (x := a + 2 * e) (y := a + b) (d := b - a) (by omega)
    rwa [show a + 2 * e + (b - a) = b + 2 * e from by omega,
      show a + b + (b - a) = 2 * b from by omega] at h
  -- Step 2: move the gap `e - f` from the `y` zero-count onto the `x` last-count.
  have h2 : (b + e + f).factorial * e.factorial ≤ (b + 2 * e).factorial * f.factorial := by
    have h := Analysis.factorial_mul_factorial_le_of_le
      (x := f) (y := b + e + f) (d := e - f) (by omega)
    rw [show f + (e - f) = e from by omega,
      show b + e + f + (e - f) = b + 2 * e from by omega] at h
    calc (b + e + f).factorial * e.factorial = e.factorial * (b + e + f).factorial :=
          Nat.mul_comm _ _
      _ ≤ (b + 2 * e).factorial * f.factorial := h
  calc (b + e + f).factorial * (a + b).factorial * e.factorial
      = (b + e + f).factorial * e.factorial * (a + b).factorial := by ring
    _ ≤ (b + 2 * e).factorial * f.factorial * (a + b).factorial :=
        Nat.mul_le_mul_right _ h2
    _ = (b + 2 * e).factorial * (a + b).factorial * f.factorial := by ring
    _ ≤ (2 * b).factorial * (a + 2 * e).factorial * f.factorial :=
        Nat.mul_le_mul_right _ h1
    _ = (a + 2 * e).factorial * (2 * b).factorial * f.factorial := by ring

/-- Consequently the `x`-leg marginal type class is the *smallest* of the three. -/
theorem multinomial_cwRectMarginalType_X_le_Y {a b e f : ℕ} (hab : a ≤ b) (heb : 2 * e ≤ b)
    (hfe : f ≤ e) :
    Nat.multinomial (Finset.univ : Finset CWBlock) (cwRectMarginalType a b e f .X) ≤
      Nat.multinomial (Finset.univ : Finset CWBlock) (cwRectMarginalType a b e f .Y) := by
  set MX : ℕ := Nat.multinomial (Finset.univ : Finset CWBlock)
    (cwRectMarginalType a b e f .X) with hMX
  set MY : ℕ := Nat.multinomial (Finset.univ : Finset CWBlock)
    (cwRectMarginalType a b e f .Y) with hMY
  have hX : (a + 2 * e).factorial * (2 * b).factorial * f.factorial * MX =
      (a + 2 * b + 2 * e + f).factorial := by
    have h := Nat.multinomial_spec (Finset.univ : Finset CWBlock)
      (cwRectMarginalType a b e f .X)
    rwa [prod_factorial_cwRectMarginalType, sum_cwRectMarginalType] at h
  have hY : (b + e + f).factorial * (a + b).factorial * e.factorial * MY =
      (a + 2 * b + 2 * e + f).factorial := by
    have h := Nat.multinomial_spec (Finset.univ : Finset CWBlock)
      (cwRectMarginalType a b e f .Y)
    rwa [prod_factorial_cwRectMarginalType, sum_cwRectMarginalType] at h
  have hfac := cwRect_marginalFactorial_Y_le_X hab heb hfe
  have hFXpos : 0 < (a + 2 * e).factorial * (2 * b).factorial * f.factorial :=
    Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)
  have hchain : (a + 2 * e).factorial * (2 * b).factorial * f.factorial * MX ≤
      (a + 2 * e).factorial * (2 * b).factorial * f.factorial * MY := by
    calc (a + 2 * e).factorial * (2 * b).factorial * f.factorial * MX
        = (a + 2 * b + 2 * e + f).factorial := hX
      _ = (b + e + f).factorial * (a + b).factorial * e.factorial * MY := hY.symm
      _ ≤ (a + 2 * e).factorial * (2 * b).factorial * f.factorial * MY :=
          Nat.mul_le_mul_right _ hfac
  exact Nat.le_of_mul_le_mul_left hchain hFXpos

/-- **The `x` leg carries the largest type-restricted fiber** when `a ≤ b`, `2e ≤ b` and `f ≤ e`.
This is the selection of [HP98, Section 7.2, p. 277], the mirror image of
`cwRectLegTypedFiber_X_le_Y`. -/
theorem cwRectLegTypedFiber_Y_le_X {a b e f : ℕ} (hab : a ≤ b) (heb : 2 * e ≤ b) (hfe : f ≤ e) :
    cwRectLegTypedFiber a b e f .Y ≤ cwRectLegTypedFiber a b e f .X := by
  have hX := multinomial_cwRectType_eq a b e f .X
  have hY := multinomial_cwRectType_eq a b e f .Y
  have hcomp := multinomial_cwRectMarginalType_X_le_Y hab heb hfe
  have hYpos : 0 < Nat.multinomial (Finset.univ : Finset CWBlock)
      (cwRectMarginalType a b e f .Y) := Nat.multinomial_pos _ _
  have hkey : cwRectLegTypedFiber a b e f .Y *
      Nat.multinomial (Finset.univ : Finset CWBlock) (cwRectMarginalType a b e f .Y) ≤
        cwRectLegTypedFiber a b e f .X *
          Nat.multinomial (Finset.univ : Finset CWBlock)
            (cwRectMarginalType a b e f .Y) := by
    calc cwRectLegTypedFiber a b e f .Y *
          Nat.multinomial (Finset.univ : Finset CWBlock) (cwRectMarginalType a b e f .Y)
        = Nat.multinomial (Finset.univ : Finset cwBlockSupport) (cwRectType a b e f) := hY.symm
      _ = cwRectLegTypedFiber a b e f .X *
          Nat.multinomial (Finset.univ : Finset CWBlock)
            (cwRectMarginalType a b e f .X) := hX
      _ ≤ cwRectLegTypedFiber a b e f .X *
          Nat.multinomial (Finset.univ : Finset CWBlock)
            (cwRectMarginalType a b e f .Y) := Nat.mul_le_mul_left _ hcomp
  exact Nat.le_of_mul_le_mul_right hkey hYpos

/-- Under the reversed Huang--Pan hypotheses the `x`-leg fiber dominates all three legs. -/
theorem cwRectLegTypedFiber_le_X {a b e f : ℕ} (hab : a ≤ b) (heb : 2 * e ≤ b) (hfe : f ≤ e)
    (c : Leg) : cwRectLegTypedFiber a b e f c ≤ cwRectLegTypedFiber a b e f .X := by
  cases c
  · exact le_rfl
  · exact cwRectLegTypedFiber_Y_le_X hab heb hfe
  · exact cwRectLegTypedFiber_Y_le_X hab heb hfe

/-! ## The method-of-types (Stirling) estimate -/

@[simp] theorem profileMass_cwRectType (a b e f : ℕ) :
    WordType.profileMass (cwRectType a b e f) = a + 2 * b + 2 * e + f := by
  unfold WordType.profileMass
  exact sum_cwRectType a b e f

@[simp] theorem proportionalCounts_cwRectType (a b e f N : ℕ) :
    WordType.proportionalCounts (cwRectType a b e f) N =
      cwRectType (a * N) (b * N) (e * N) (f * N) := by
  funext s
  rcases s with ⟨s, hs⟩
  show cwRectAddressCount a b e f s * N = cwRectAddressCount (a * N) (b * N) (e * N) (f * N) s
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [cwRectAddressCount_cw200, cwRectAddressCount_cw020, cwRectAddressCount_cw002,
      cwRectAddressCount_cw011, cwRectAddressCount_cw101, cwRectAddressCount_cw110]

/-- The entropy growth base of the rectangular profile:
`(a+2b+2e+f)^(a+2b+2e+f) / (a^a · b^{2b} · e^{2e} · f^f)`. -/
theorem proportionalEntropyBase_cwRectType {a b e f : ℕ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (hf : 0 < f) :
    WordType.proportionalEntropyBase (cwRectType a b e f) =
      ((a + 2 * b + 2 * e + f : ℕ) : ℝ) ^ (a + 2 * b + 2 * e + f) /
        ((a : ℝ) ^ a * (b : ℝ) ^ (2 * b) * (e : ℝ) ^ (2 * e) * (f : ℝ) ^ f) := by
  have haR : ((a : ℝ)) ≠ 0 := by positivity
  have hbR : ((b : ℝ)) ≠ 0 := by positivity
  have heR : ((e : ℝ)) ≠ 0 := by positivity
  have hfR : ((f : ℝ)) ≠ 0 := by positivity
  have hene : (Real.exp 1) ≠ 0 := Real.exp_ne_zero 1
  have hprod :
      (∏ s : cwBlockSupport, WordType.factorialEntropyTerm (cwRectType a b e f s)) =
        WordType.factorialEntropyTerm f * (WordType.factorialEntropyTerm e *
          (WordType.factorialEntropyTerm e * (WordType.factorialEntropyTerm a *
            (WordType.factorialEntropyTerm b * WordType.factorialEntropyTerm b)))) := by
    have h : (∏ s : cwBlockSupport, WordType.factorialEntropyTerm (cwRectType a b e f s)) =
        ∏ s ∈ cwBlockSupport, WordType.factorialEntropyTerm (cwRectAddressCount a b e f s) :=
      (Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ WordType.factorialEntropyTerm (cwRectAddressCount a b e f s))).symm
    rw [h, prod_cwBlockSupport, cwRectAddressCount_cw200, cwRectAddressCount_cw020,
      cwRectAddressCount_cw002, cwRectAddressCount_cw011, cwRectAddressCount_cw101,
      cwRectAddressCount_cw110]
  unfold WordType.proportionalEntropyBase
  rw [hprod, profileMass_cwRectType]
  unfold WordType.factorialEntropyTerm
  simp only [div_pow]
  have hee : (Real.exp 1) ^ (a + 2 * b + 2 * e + f) =
      Real.exp 1 ^ f * (Real.exp 1 ^ e * (Real.exp 1 ^ e *
        (Real.exp 1 ^ a * (Real.exp 1 ^ b * Real.exp 1 ^ b)))) := by
    rw [show a + 2 * b + 2 * e + f = f + (e + (e + (a + (b + b)))) from by ring]
    rw [pow_add, pow_add, pow_add, pow_add, pow_add]
  have hbb : ((b : ℝ)) ^ (2 * b) = (b : ℝ) ^ b * (b : ℝ) ^ b := by
    rw [two_mul, pow_add]
  have hee2 : ((e : ℝ)) ^ (2 * e) = (e : ℝ) ^ e * (e : ℝ) ^ e := by
    rw [two_mul, pow_add]
  rw [hee, hbb, hee2]
  field_simp

/-- **Method of types for the rectangular profile.**  This is the Stirling step of
[HP98, p. 277]. -/
theorem cwRectType_entropyBase_pow_le_loss_mul_card {a b e f : ℕ} (ha : 0 < a) (hb : 0 < b)
    (he : 0 < e) (hf : 0 < f) {N : ℕ} (hN : 0 < N) :
    (((a + 2 * b + 2 * e + f : ℕ) : ℝ) ^ (a + 2 * b + 2 * e + f) /
        ((a : ℝ) ^ a * (b : ℝ) ^ (2 * b) * (e : ℝ) ^ (2 * e) * (f : ℝ) ^ f)) ^ N ≤
      WordType.proportionalMultinomialLoss (cwRectType a b e f) N *
        ((cwRectTypeWords (a * N) (b * N) (e * N) (f * N)).card : ℝ) := by
  haveI : Nonempty cwBlockSupport := ⟨cw200S⟩
  have hmul :
      ((cwRectTypeWords (a * N) (b * N) (e * N) (f * N)).card : ℝ) =
        (Nat.multinomial Finset.univ
          (WordType.proportionalCounts (cwRectType a b e f) N) : ℝ) := by
    rw [proportionalCounts_cwRectType,
      card_cwRectTypeWords (a := a * N) (b := b * N) (e := e * N) (f := f * N) (by positivity)]
  rw [hmul, ← proportionalEntropyBase_cwRectType ha hb he hf]
  exact WordType.proportionalEntropyBase_pow_le_loss_mul_multinomial
    (cwRectType a b e f) N (cwRectType_pos ha hb he hf) hN

theorem cwRectType_proportionalMultinomialLoss_subexponential (a b e f : ℕ) :
    Growth.Subexponential (WordType.proportionalMultinomialLoss (cwRectType a b e f)) :=
  WordType.proportionalMultinomialLoss_subexponential _

/-! ## Regression at `r = 1`

The existing checked client `Examples/CoppersmithWinogradFirstPowerHashing.lean` uses the type
`(9519k, 9519k, 481k, 481k)` in the parameters above, i.e. `r = 1` and `β = L/N = 481/10000`. -/

/-- **Faithfulness.**  At `(a, b, e, f) = (9519k, 9519k, 481k, 481k)` the rectangular profile *is*
the checked first-power type of `Examples/CoppersmithWinogradFirstPowerHashing.lean`. -/
@[simp] theorem cwRectType_firstPower (k : ℕ) :
    cwRectType (9519 * k) (9519 * k) (481 * k) (481 * k) = cwFirstPowerNaturalType k := by
  funext s
  rcases s with ⟨s, hs⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [cwRectType, cwFirstPowerNaturalType, cwFirstPowerAddressCount, cw200, cw020, cw002,
      cw011, cw101, cw110, cwBlockAddress]

/-- Regression: the rectangular depth at the first-power parameters is `cwFirstPowerDepth`. -/
@[simp] theorem cwRectDepth_firstPower (k : ℕ) :
    cwRectDepth (9519 * k) (9519 * k) (481 * k) (481 * k) = cwFirstPowerDepth k := by
  unfold cwRectDepth cwFirstPowerDepth
  omega

/-- Regression: the rectangular leg marginals at the first-power parameters are the checked
ternary marginal `(10481k, 19038k, 481k)`. -/
@[simp] theorem cwRectMarginalType_firstPower (k : ℕ) (c : Leg) :
    cwRectMarginalType (9519 * k) (9519 * k) (481 * k) (481 * k) c =
      cwFirstPowerMarginalType k := by
  funext β
  cases c <;> cases β <;>
    simp only [cwRectMarginalType, cwFirstPowerMarginalType] <;> ring

/-- Regression: at the first-power parameters all three leg fibers agree, as they must. -/
theorem cwRectLegTypedFiber_firstPower_eq (k : ℕ) (c : Leg) :
    cwRectLegTypedFiber (9519 * k) (9519 * k) (481 * k) (481 * k) c =
      cwRectLegTypedFiber (9519 * k) (9519 * k) (481 * k) (481 * k) .Y := by
  have h2 : 2 * (481 * k) = 481 * k + 481 * k := by ring
  have h3 : 2 * (9519 * k) = 9519 * k + 9519 * k := by ring
  cases c
  · simp only [cwRectLegTypedFiber, h2, h3, Nat.add_assoc]
  · rfl
  · rfl

end AlgebraicComplexity.Examples
