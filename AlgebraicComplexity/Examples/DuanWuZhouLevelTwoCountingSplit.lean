/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCounting
import AlgebraicComplexity.Combinatorics.CompatibleSplitCount

/-!
# The section 6.3 splits, as a concrete `SplitRequirements`

`Combinatorics/CompatibleSplitCount.lean` (M-DWZ5) develops `[DuanWuZhou2022]`'s combination loss
generically, over an arbitrary `SplitRequirements C L Z` --- the three-field record
`(zIndex, boundary, splitCount)` from which `def:global-compatible`, `def:useful_g` and
`lemma:pcomp_g` are all read off.  Everything there is proved for an *arbitrary* such record; what
was missing, and what `better_bound/dwz_endpoint_prep/PREP.md` section 4.3 calls estimates (e) and
(f), is the concrete record at the section 6.3 parameters.  This module supplies it.

## The splits

A level-two `Z`-index `k` splits as `k = k_l + k_r` with `k_l, k_r` in `{0, 1, 2}`, so the split
alphabet is `L = Fin 3` indexed by `k_l`.  Section 6.3 prescribes

* `k = 0`: the point mass at `k_l = 0`;  `k = 4`: the point mass at `k_l = 2`;
* `k = 1`: uniform on `{0, 1}`;  `k = 3`: uniform on `{1, 2}`;
* `k = 2` on `(0,2,2)` and `(2,0,2)`: `(a, 1 - 2a, a)` with `a = 0.03477403`;
* `k = 2` on `(1,1,2)`: `(b, 1 - 2b, b)` with `b = 0.00021015`.

`a` and `b` are exact rationals over `10 ^ 8`, so the smallest word length carrying every one of
these as an *integer* count is `2 * (10 ^ 8) ^ 2`.  `dwz63SplitCount` is that base table --- the
45 integers `n_0 * alpha(c) * alphatilde_c(l)` --- and `dwz63Split k` repeats it `k` times.  Its
consistency hypothesis is

`dwz63Split_refinesType :`
`  (dwz63Split k).RefinesType (proportionalCounts dwz63Alpha (2 * 10 ^ 8 * k))`,

i.e. the split table refines the very 15-cell profile of `Examples/DuanWuZhouLevelTwoCounting.lean`.
That single identity is what connects the compatibility layer to the marginal layer: the same
`dwz63Alpha` supplies `N_alpha` upstream and the split masses here.

## Estimates (e) and (f)

`dwz63_card_compatibleSet_eq_prod` and `dwz63_card_typicalSet_eq_prod` are the exact,
division-free product closed forms --- `lemma:pcomp_g`'s numerator and denominator --- specialized
to section 6.3, and `dwz63_compatibleType_inr` / `dwz63_typicalType` evaluate every one of their
rows to an explicit integer table.  Two of those rows carry the whole content of the `a`- and
`b`-splits:

* the pooled interior requirement at `k = 2` is `(b, 1 - 2b, b)` scaled by `alpha(+,+,2)`;
* the typicalness row at `k = 2` is `(P, Q, P)` with `2 P + Q = alpha_Z(2) * 10 ^ 8 * 2`, the exact
  identity PREP section 6's data appendix records.

Everything here is finite and exact: no rate, no `o(n)`, no enclosure.  The entropy comparison that
turns these cardinalities into `alphabar_p` is the *loss-free upper* direction of the method of
types for (e), and the support-restricted lower direction for (f); both are supplied generically by
`Combinatorics/TypeClassCounting.lean` once these tables are in hand.

## Position in the library

Layer 4 (a client).  It constructs one record and instantiates committed theorems at it; no new
counting argument is introduced.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3, `def:global-compatible`, `def:useful_g`, `lemma:pcomp_g`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity

noncomputable section

/-! ## The base split table -/

/-- **The prescribed splits of `[DuanWuZhou2022]` section 6.3, in integral form.**

Row `c` is the component `c` of `dwz63Alpha`, column `l` is the left half `k_l` of its `Z`-index.
The entries are `n_0 * alpha(c) * alphatilde_c(l)` at the base word length
`n_0 = 2 * (10 ^ 8) ^ 2 = 2 * 10 ^ 16`, the smallest length at which the `a`- and `b`-splits are
integral.  Each row sums to `2 * 10 ^ 8 * alpha(c)`. -/
def dwz63SplitCount : Fin 15 → Fin 3 → ℕ :=
  ![![0, 0, 4172000000000],
    ![0, 121115300000000, 121115300000000],
    ![72100091287670, 1929188817424660, 72100091287670],
    ![133331800000000, 133331800000000, 0],
    ![4946200000000, 0, 0],
    ![0, 121115300000000, 121115300000000],
    ![844324824690, 4016035950350620, 844324824690],
    ![2073445800000000, 2073445800000000, 0],
    ![250351600000000, 0, 0],
    ![72100091287670, 1929188817424660, 72100091287670],
    ![2073445800000000, 2073445800000000, 0],
    ![2009158200000000, 0, 0],
    ![133331800000000, 133331800000000, 0],
    ![250351600000000, 0, 0],
    ![4946200000000, 0, 0]]

/-- **The section 6.3 splitting data**, at word length `2 * 10 ^ 16 * k`.

`zIndex` and `boundary` are the third coordinate and the degeneracy test `i = 0 or j = 0` of
`Examples/DuanWuZhouLevelTwoCounting.lean`; `splitCount` is the base table repeated `k` times.
This is the record every theorem of `Combinatorics/CompatibleSplitCount.lean` is stated over. -/
def dwz63Split (k : ℕ) : CompatibleSplit.SplitRequirements (Fin 15) (Fin 3) (Fin 5) where
  zIndex := dwz63ZIndex
  boundary := dwz63Boundary
  splitCount c l := dwz63SplitCount c l * k

/-- **The standing consistency hypothesis of `lemma:pcomp_g`, at section 6.3.**

The prescribed splits refine the 15-cell distribution: summing a component's split over the three
left halves returns `2 * 10 ^ 8` times its `alpha`-weight.  This is the identity that ties the
compatibility layer to `Examples/DuanWuZhouLevelTwoCounting.lean`'s marginal layer --- both are
about the same `dwz63Alpha`. -/
theorem dwz63Split_refinesType (k : ℕ) :
    (dwz63Split k).RefinesType (WordType.proportionalCounts dwz63Alpha (200000000 * k)) := by
  intro c
  fin_cases c <;>
    simp [dwz63Split, dwz63SplitCount, dwz63Alpha, WordType.proportionalCounts,
      Fin.sum_univ_three] <;>
    ring

/-- The base word length of one repetition: `2 * (10 ^ 8) ^ 2 = 2 * 10 ^ 16`. -/
theorem dwz63Split_profileMass (k : ℕ) :
    WordType.profileMass (WordType.proportionalCounts dwz63Alpha (200000000 * k)) =
      20000000000000000 * k := by
  show ∑ c, dwz63Alpha c * (200000000 * k) = 20000000000000000 * k
  rw [← Finset.sum_mul]
  show WordType.profileMass dwz63Alpha * (200000000 * k) = 20000000000000000 * k
  rw [profileMass_dwz63Alpha]
  ring

/-! ## The requirement rows -/

/-- **The pooled interior requirement rows** `alpha(+,+,k) * alphatilde^avg_{+,+,k}`, in integral
form at the base word length.  Only `k = 0, 1, 2` are nonzero: no interior component has
`Z`-index `3` or `4`.  The `k = 2` row is exactly the `b`-split of `(1,1,2)`. -/
def dwz63PooledCount : Fin 5 → Fin 3 → ℕ :=
  ![![2509861400000000, 0, 0],
    ![4146891600000000, 4146891600000000, 0],
    ![844324824690, 4016035950350620, 844324824690],
    ![0, 0, 0],
    ![0, 0, 0]]

/-- **The typicalness rows** `gamma`, i.e. `alpha_Z(k) * alphatilde^avg_{*,*,k}`, in integral form
at the base word length.  The `k = 2` row is `(P, Q, P)` with
`2 P + Q = 8164502600000000 = 2 * 10 ^ 8 * alpha_Z(2) * 10 ^ 8 / 10 ^ 8`, the exact identity of
PREP section 6's data appendix. -/
def dwz63AverageCount : Fin 5 → Fin 3 → ℕ :=
  ![![2519753800000000, 0, 0],
    ![4413555200000000, 4413555200000000, 0],
    ![145044507400030, 7874413585199940, 145044507400030],
    ![0, 242230600000000, 242230600000000],
    ![0, 0, 4172000000000]]

/-- The boundary rows of the compatibility profile are the boundary components' own prescribed
splits: DWZ's requirement family (a). -/
theorem dwz63_compatibleType_inl (k : ℕ) (c : Fin 15) (l : Fin 3) :
    (dwz63Split k).compatibleType (Sum.inl c, l) =
      if dwz63Boundary c then dwz63SplitCount c l * k else 0 := by
  exact (dwz63Split k).compatibleType_inl c l

/-- **The pooled rows of the compatibility profile, evaluated.**  DWZ's requirement family (c):
the interior components sharing a `Z`-index are pooled into one requirement, whose split is the
`alpha`-weighted average.  At `k = 2` this is precisely the `b`-split of `(1,1,2)`. -/
theorem dwz63_compatibleType_inr (k : ℕ) (z : Fin 5) (l : Fin 3) :
    (dwz63Split k).compatibleType (Sum.inr z, l) = dwz63PooledCount z l * k := by
  rw [CompatibleSplit.SplitRequirements.compatibleType_inr]
  fin_cases z <;> fin_cases l <;>
    simp [CompatibleSplit.SplitRequirements.requirement, dwz63Split, dwz63Boundary, dwz63ZIndex,
      dwz63SplitCount, dwz63PooledCount, Fin.sum_univ_succ] <;>
    ring

/-- **The typicalness profile `gamma`, evaluated.**  Row `k` pools *all* components of `Z`-index
`k`, boundary and interior alike; at `k = 2` this mixes the `a`-split of `(0,2,2)` and `(2,0,2)`
with the `b`-split of `(1,1,2)`. -/
theorem dwz63_typicalType (k : ℕ) (z : Fin 5) (l : Fin 3) :
    (dwz63Split k).typicalType (z, l) = dwz63AverageCount z l * k := by
  rw [CompatibleSplit.SplitRequirements.typicalType_apply]
  fin_cases z <;> fin_cases l <;>
    simp [dwz63Split, dwz63ZIndex, dwz63SplitCount, dwz63AverageCount, Fin.sum_univ_succ] <;>
    ring

/-! ## Estimates (e) and (f): the exact block counts -/

variable {n : ℕ}

/-- **Estimate (e) of `PREP.md` section 4.3, in exact finite form.**  The number of small blocks
compatible with a large triple of the section 6.3 type is the product, over the nine boundary
requirements and the five pooled requirements, of that requirement's multinomial coefficient. -/
theorem dwz63_card_compatibleSet_eq_prod (k : ℕ) (comp : Fin n → Fin 15)
    (hcomp : WordType.multiplicity comp =
      WordType.proportionalCounts dwz63Alpha (200000000 * k)) :
    ((dwz63Split k).compatibleSet comp).card =
      ∏ r : Fin 15 ⊕ Fin 5,
        Nat.multinomial Finset.univ fun l ↦ (dwz63Split k).compatibleType (r, l) :=
  (dwz63Split k).card_compatibleSet_eq_prod (dwz63Split_refinesType k) comp hcomp

/-- **Estimate (f) of `PREP.md` section 4.3, in exact finite form.**  `|T_K|` is the product over
the five `Z`-indices of the multinomial coefficient of the average split at that index. -/
theorem dwz63_card_typicalSet_eq_prod (k : ℕ) (comp : Fin n → Fin 15)
    (hcomp : WordType.multiplicity comp =
      WordType.proportionalCounts dwz63Alpha (200000000 * k)) :
    ((dwz63Split k).typicalSet ((dwz63Split k).zIndex ∘ comp)).card =
      ∏ z : Fin 5, Nat.multinomial Finset.univ fun l ↦ (dwz63Split k).typicalType (z, l) :=
  (dwz63Split k).card_typicalSet_eq_prod (dwz63Split_refinesType k) comp hcomp

/-- The useful-block count `|Z^M|` at section 6.3: the product over **all** fifteen components. -/
theorem dwz63_card_usefulSet_eq_prod (k : ℕ) (comp : Fin n → Fin 15)
    (hcomp : WordType.multiplicity comp =
      WordType.proportionalCounts dwz63Alpha (200000000 * k)) :
    ((dwz63Split k).usefulSet comp).card =
      ∏ c : Fin 15, Nat.multinomial Finset.univ ((dwz63Split k).splitCount c) :=
  (dwz63Split k).card_usefulSet_eq_prod (dwz63Split_refinesType k) comp hcomp

/-- The combination loss of section 6.3 is a genuine gain in block count: every useful block is
compatible. -/
theorem dwz63_card_usefulSet_le_card_compatibleSet (k : ℕ) (comp : Fin n → Fin 15) :
    ((dwz63Split k).usefulSet comp).card ≤ ((dwz63Split k).compatibleSet comp).card :=
  (dwz63Split k).card_usefulSet_le_card_compatibleSet comp

/-! ## Anti-vacuity -/

/-- Compatible small blocks exist at section 6.3's parameters: the numerator of `lemma:pcomp_g` is
not zero. -/
theorem dwz63_compatibleSet_nonempty (k : ℕ) (comp : Fin n → Fin 15)
    (hcomp : WordType.multiplicity comp =
      WordType.proportionalCounts dwz63Alpha (200000000 * k)) :
    ((dwz63Split k).compatibleSet comp).Nonempty :=
  (dwz63Split k).compatibleSet_nonempty (dwz63Split_refinesType k) comp hcomp

/-- Typical small blocks exist at section 6.3's parameters: the denominator of `lemma:pcomp_g` is
not zero. -/
theorem dwz63_typicalSet_nonempty (k : ℕ) (comp : Fin n → Fin 15)
    (hcomp : WordType.multiplicity comp =
      WordType.proportionalCounts dwz63Alpha (200000000 * k)) :
    ((dwz63Split k).typicalSet ((dwz63Split k).zIndex ∘ comp)).Nonempty :=
  (dwz63Split k).typicalSet_nonempty (dwz63Split_refinesType k) comp hcomp

/-- **The competitor pair count of `claim:hole_frac_low` at section 6.3.**  This is the exact
identity the second branch of the modulus `M_0` is chosen to dominate; every factor is a finite
cardinality supplied by the closed forms above. -/
theorem dwz63_card_matchableCompatible_mul_card_typicalSet (k : ℕ) {K : Fin n → Fin 5}
    {comp₀ : Fin n → Fin 15}
    (hcomp₀ : comp₀ ∈ (dwz63Split k).matchable
      (WordType.proportionalCounts dwz63Alpha (200000000 * k)) K)
    {w : Fin n → Fin 3} (hw : w ∈ (dwz63Split k).typicalSet K) :
    ((dwz63Split k).matchableCompatible
        (WordType.proportionalCounts dwz63Alpha (200000000 * k)) K w).card *
        ((dwz63Split k).typicalSet K).card =
      ((dwz63Split k).matchable
        (WordType.proportionalCounts dwz63Alpha (200000000 * k)) K).card *
        ((dwz63Split k).compatibleSet comp₀).card :=
  (dwz63Split k).card_matchableCompatible_mul_card_typicalSet hcomp₀ hw

end

end AlgebraicComplexity.Examples
