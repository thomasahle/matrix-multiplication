/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Degeneration
import AlgebraicComplexity.Tensor.DirectSum

/-!
# The free-lunch speedup theorem

This file proves the *free-lunch speedup theorem* of Alman and Li
([AlmanLi2026], Theorem 5.1, p. 14, together with its degeneration bootstrap Corollary 5.1,
p. 15) in the basis-free polynomial-degeneration language of this library.

## Statement

Let `S` be a tensor with legs `V`, let `f` carry `S` to a tensor `T` with legs `W`, and let `g`
be a second family of leg maps with target legs `W'`.  Write both families into the *block sum*
`W c × W' c` by post-composing with the two inclusions:

```text
FL c = inl ∘ f c,      GR c = inr ∘ g c.
```

If the three *mixed* blocks that involve the `g`-component on the `Z` leg but not on all three
legs vanish,

```text
(FL, FL, GR) S = 0,   (GR, FL, GR) S = 0,   (FL, GR, GR) S = 0,
```

then `S` degenerates to the direct sum `T ⊕ T'`, where `T' = (GR,GR,GR) S`.  The direct summand
`T'` is obtained "for free": nothing is added to the source `S`.

## What the paper needs two parameters for, and why this file does not

Alman and Li prove Theorem 5.1 for a *restriction* `T ≤ S` and then bootstrap it to a
*degeneration* `T ⊴ S` (their Corollary 5.1) by regarding the degeneration as a restriction of
`F(λ)`-tensors, applying Theorem 5.1 over `F(λ)` with a **second** parameter `ε`, and finally
substituting `ε = λ^k` for a sufficiently large `k`.  That two-parameter detour is what a
`Tensor/FunctionFieldDegeneration.lean` module would have had to formalize.

It is unnecessary.  The junk blocks that the `ε`-degeneration removes are killed by *any*
sufficiently large power of the degeneration parameter, and in the constructive polynomial
language of `Tensor/Degeneration.lean` the required exponents are visible: they are computed
from the two displayed leading degrees `d` and `d'`.  `polynomialDegeneratesAt_add_of_mixed_eq_zero`
below therefore performs the whole construction with the *single* parameter `ε` already present,
choosing the shifts

```text
FL : (0, 0, d + d' + 2),      GR : (d + 1, d + 1, 0),
```

which places both surviving diagonal blocks in degree `2d + d' + 2` and every junk block strictly
above it.  Specializing to `d = d' = 0` and constant map families recovers the restriction form
(Theorem 5.1) at leading degree `2`, exactly the `diag(1,ε) ⊗ diag(1,ε) ⊗ diag(ε²,1)` certificate
displayed in the paper's proof.

So the in-scope constructive layer of [AlmanLi2026] needs **no** function-field or two-parameter
degeneration notion; the existing single-parameter machinery suffices, and this file is the
missing piece.

## Main results

* `polynomialTransform_ofLegs_monomial`, `polynomialTransform_ofLegs_shift`,
  `polynomialTransform_ofLegs_postcompose`: the three structural laws of `polynomialTransform`
  used below.  They belong to `Tensor/Degeneration.lean` and are kept here only to avoid editing
  that shared file.
* `polynomialDegeneratesAt_add_of_mixed_eq_zero` and its direct-sum specialization
  `polynomialDegeneratesAt_directSum_of_blockPoly`: the polynomial (degeneration) form of the
  free-lunch speedup theorem, subsuming [AlmanLi2026, Corollary 5.1].
* `polynomialDegeneratesAt_two_add_of_mixed_map_eq_zero` and its direct-sum specialization
  `polynomialDegeneratesAt_two_directSum_of_mixed_map_eq_zero`: the restriction form,
  [AlmanLi2026, Theorem 5.1].

## Non-goals

The paper's *maximal* choices `A' = {u : (u ⊗ B ⊗ C')S = 0}` and `B' = {v : (A ⊗ v ⊗ C')S = 0}`
are one legal instance of the family `g` below; nothing in the degeneration argument uses their
maximality, so the hypotheses here are strictly weaker than the paper's.  Maximality matters only
for the *size* of the extracted summand, i.e. for [AlmanLi2026, Proposition 5.3], which is a
statement about matrix rank and is not proved here.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Section 5.
* V. Strassen, *Relative bilinear complexity and matrix multiplication*, J. reine angew. Math.
  375/376 (1987) ([Strassen1987]); D. Coppersmith and S. Winograd, *On the asymptotic complexity
  of matrix multiplication*, SIAM J. Comput. 11 (1982) ([CoppersmithWinograd1982], Theorem A).
-/

namespace AlgebraicComplexity.Tensor

universe u v w w' x

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w} {W' : Leg → Type w'} {U : Leg → Type x}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
variable [∀ c, AddCommMonoid (W' c)] [∀ c, Module K (W' c)]
variable [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]

/-! ### Structural laws of `polynomialTransform` -/

/-- Polynomial transformation by three monomial map families `ε^{dx} fx`, `ε^{dy} fy`,
`ε^{dz} fz` produces the single monomial `ε^{dx+dy+dz} (fx ⊗ fy ⊗ fz) T`. -/
theorem polynomialTransform_ofLegs_monomial
    (dx dy dz : ℕ) (fx : V .X →ₗ[K] W .X) (fy : V .Y →ₗ[K] W .Y) (fz : V .Z →ₗ[K] W .Z)
    (T : Tensor3 K V) :
    polynomialTransform (ofLegs (PolynomialVector.monomial dx fx)
        (PolynomialVector.monomial dy fy) (PolynomialVector.monomial dz fz)) T =
      PolynomialVector.monomial (dx + dy + dz) (map (ofLegs fx fy fz) T) := by
  classical
  simp only [polynomialTransform, ofLegs_X, ofLegs_Y, ofLegs_Z, PolynomialVector.monomial]
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
    Finsupp.sum_single_index (by simp)]

/-- Multiplying each of the three map families by a power of the parameter multiplies the
transformed path by the product of those powers. -/
theorem polynomialTransform_ofLegs_shift (nx ny nz : ℕ)
    (AX : PolynomialLinearMap K (V .X) (W .X))
    (AY : PolynomialLinearMap K (V .Y) (W .Y))
    (AZ : PolynomialLinearMap K (V .Z) (W .Z)) (T : Tensor3 K V) :
    polynomialTransform (ofLegs (PolynomialVector.shift nx AX)
        (PolynomialVector.shift ny AY) (PolynomialVector.shift nz AZ)) T =
      PolynomialVector.shift (nx + ny + nz)
        (polynomialTransform (ofLegs AX AY AZ) T) := by
  classical
  induction AX using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp only [PolynomialVector.shift_add, polynomialTransform_add_maps_X, ha, hb,
        PolynomialVector.shift_add]
  | single dx fx =>
      induction AY using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          simp only [PolynomialVector.shift_add, polynomialTransform_add_maps_Y, ha, hb,
            PolynomialVector.shift_add]
      | single dy fy =>
          induction AZ using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              simp only [PolynomialVector.shift_add, polynomialTransform_add_maps_Z, ha, hb,
                PolynomialVector.shift_add]
          | single dz fz =>
              show polynomialTransform (ofLegs
                  (PolynomialVector.shift nx (PolynomialVector.monomial dx fx))
                  (PolynomialVector.shift ny (PolynomialVector.monomial dy fy))
                  (PolynomialVector.shift nz (PolynomialVector.monomial dz fz))) T =
                PolynomialVector.shift (nx + ny + nz)
                  (polynomialTransform (ofLegs (PolynomialVector.monomial dx fx)
                    (PolynomialVector.monomial dy fy)
                    (PolynomialVector.monomial dz fz)) T)
              rw [PolynomialVector.shift_monomial, PolynomialVector.shift_monomial,
                PolynomialVector.shift_monomial, polynomialTransform_ofLegs_monomial,
                polynomialTransform_ofLegs_monomial, PolynomialVector.shift_monomial]
              congr 1
              omega

/-- Post-composition with a fixed linear map, as a linear map between hom-spaces. -/
def postcomposeₗ {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (h : N →ₗ[K] P) : (M →ₗ[K] N) →ₗ[K] (M →ₗ[K] P) where
  toFun φ := h ∘ₗ φ
  map_add' φ ψ := by ext m; simp
  map_smul' r φ := by ext m; simp

@[simp] theorem postcomposeₗ_apply {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (h : N →ₗ[K] P) (φ : M →ₗ[K] N) : postcomposeₗ h φ = h ∘ₗ φ := rfl

/-- Post-composing the three map families with fixed leg maps `hx`, `hy`, `hz` post-composes the
transformed path with the induced tensor map. -/
theorem polynomialTransform_ofLegs_postcompose
    (hx : W .X →ₗ[K] U .X) (hy : W .Y →ₗ[K] U .Y) (hz : W .Z →ₗ[K] U .Z)
    (AX : PolynomialLinearMap K (V .X) (W .X))
    (AY : PolynomialLinearMap K (V .Y) (W .Y))
    (AZ : PolynomialLinearMap K (V .Z) (W .Z)) (T : Tensor3 K V) :
    polynomialTransform (ofLegs
        (PolynomialVector.mapLinear (postcomposeₗ hx) AX)
        (PolynomialVector.mapLinear (postcomposeₗ hy) AY)
        (PolynomialVector.mapLinear (postcomposeₗ hz) AZ)) T =
      PolynomialVector.mapLinear (map (ofLegs hx hy hz))
        (polynomialTransform (ofLegs AX AY AZ) T) := by
  classical
  induction AX using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp only [map_add, polynomialTransform_add_maps_X, ha, hb, map_add]
  | single dx fx =>
      induction AY using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          simp only [map_add, polynomialTransform_add_maps_Y, ha, hb, map_add]
      | single dy fy =>
          induction AZ using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              simp only [map_add, polynomialTransform_add_maps_Z, ha, hb, map_add]
          | single dz fz =>
              show polynomialTransform (ofLegs
                  (PolynomialVector.mapLinear (postcomposeₗ hx)
                    (PolynomialVector.monomial dx fx))
                  (PolynomialVector.mapLinear (postcomposeₗ hy)
                    (PolynomialVector.monomial dy fy))
                  (PolynomialVector.mapLinear (postcomposeₗ hz)
                    (PolynomialVector.monomial dz fz))) T =
                PolynomialVector.mapLinear (map (ofLegs hx hy hz))
                  (polynomialTransform (ofLegs (PolynomialVector.monomial dx fx)
                    (PolynomialVector.monomial dy fy)
                    (PolynomialVector.monomial dz fz)) T)
              rw [PolynomialVector.mapLinear_monomial, PolynomialVector.mapLinear_monomial,
                PolynomialVector.mapLinear_monomial, polynomialTransform_ofLegs_monomial,
                polynomialTransform_ofLegs_monomial, PolynomialVector.mapLinear_monomial]
              congr 1
              rw [show (ofLegs (postcomposeₗ hx fx) (postcomposeₗ hy fy) (postcomposeₗ hz fz) :
                    ∀ c, V c →ₗ[K] U c) =
                  fun c ↦ (ofLegs (V := fun i ↦ W i →ₗ[K] U i) hx hy hz c) ∘ₗ
                    (ofLegs (V := fun i ↦ V i →ₗ[K] W i) fx fy fz c) by
                funext c; cases c <;> rfl, map_comp]
              rfl

/-! ### Block map families -/

/-- The left block of a family of leg maps: `inl ∘ f c : V c →ₗ W c × W' c`.

The extra-summand leg family `W'` is an explicit argument because it is not determined by `f`. -/
def directSumLeftMaps (W' : Leg → Type w')
    [∀ c, AddCommMonoid (W' c)] [∀ c, Module K (W' c)]
    (f : ∀ c, V c →ₗ[K] W c) : ∀ c, V c →ₗ[K] W c × W' c :=
  fun c ↦ LinearMap.inl K (W c) (W' c) ∘ₗ f c

/-- The right block of a family of leg maps: `inr ∘ g c : V c →ₗ W c × W' c`. -/
def directSumRightMaps (W : Leg → Type w)
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    (g : ∀ c, V c →ₗ[K] W' c) : ∀ c, V c →ₗ[K] W c × W' c :=
  fun c ↦ LinearMap.inr K (W c) (W' c) ∘ₗ g c

/-- The left block of a *polynomial* family of leg maps. -/
noncomputable def directSumLeftPolyMaps (W' : Leg → Type w')
    [∀ c, AddCommMonoid (W' c)] [∀ c, Module K (W' c)]
    (A : ∀ c, PolynomialLinearMap K (V c) (W c)) :
    ∀ c, PolynomialLinearMap K (V c) (W c × W' c) :=
  fun c ↦ PolynomialVector.mapLinear (postcomposeₗ (LinearMap.inl K (W c) (W' c))) (A c)

/-- The right block of a *polynomial* family of leg maps. -/
noncomputable def directSumRightPolyMaps (W : Leg → Type w)
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    (B : ∀ c, PolynomialLinearMap K (V c) (W' c)) :
    ∀ c, PolynomialLinearMap K (V c) (W c × W' c) :=
  fun c ↦ PolynomialVector.mapLinear (postcomposeₗ (LinearMap.inr K (W c) (W' c))) (B c)

/-- Transforming by the all-left block family is transforming by the original family and then
including into the left summand. -/
theorem polynomialTransform_directSumLeftPolyMaps
    (A : ∀ c, PolynomialLinearMap K (V c) (W c)) (S : Tensor3 K V) :
    polynomialTransform (directSumLeftPolyMaps (K := K) W' A) S =
      PolynomialVector.mapLinear (map (includeLeft (K := K) (V := W) (W := W')))
        (polynomialTransform A S) := by
  have hA : A = ofLegs (A .X) (A .Y) (A .Z) := (ofLegs_eta A).symm
  have h := polynomialTransform_ofLegs_postcompose
    (K := K) (V := V) (U := fun c ↦ W c × W' c)
    (LinearMap.inl K (W .X) (W' .X)) (LinearMap.inl K (W .Y) (W' .Y))
    (LinearMap.inl K (W .Z) (W' .Z)) (A .X) (A .Y) (A .Z) S
  rw [show directSumLeftPolyMaps (K := K) W' A =
      ofLegs (PolynomialVector.mapLinear (postcomposeₗ (LinearMap.inl K (W .X) (W' .X))) (A .X))
        (PolynomialVector.mapLinear (postcomposeₗ (LinearMap.inl K (W .Y) (W' .Y))) (A .Y))
        (PolynomialVector.mapLinear (postcomposeₗ (LinearMap.inl K (W .Z) (W' .Z))) (A .Z)) by
    funext c; cases c <;> rfl]
  rw [h, ← hA, show (ofLegs (LinearMap.inl K (W .X) (W' .X)) (LinearMap.inl K (W .Y) (W' .Y))
      (LinearMap.inl K (W .Z) (W' .Z)) : ∀ c, W c →ₗ[K] W c × W' c) =
      includeLeft (K := K) (V := W) (W := W') by funext c; cases c <;> rfl]

/-- Transforming by the all-right block family is transforming by the original family and then
including into the right summand. -/
theorem polynomialTransform_directSumRightPolyMaps
    (B : ∀ c, PolynomialLinearMap K (V c) (W' c)) (S : Tensor3 K V) :
    polynomialTransform (directSumRightPolyMaps (K := K) W B) S =
      PolynomialVector.mapLinear (map (includeRight (K := K) (V := W) (W := W')))
        (polynomialTransform B S) := by
  have hB : B = ofLegs (B .X) (B .Y) (B .Z) := (ofLegs_eta B).symm
  have h := polynomialTransform_ofLegs_postcompose
    (K := K) (V := V) (U := fun c ↦ W c × W' c)
    (LinearMap.inr K (W .X) (W' .X)) (LinearMap.inr K (W .Y) (W' .Y))
    (LinearMap.inr K (W .Z) (W' .Z)) (B .X) (B .Y) (B .Z) S
  rw [show directSumRightPolyMaps (K := K) W B =
      ofLegs (PolynomialVector.mapLinear (postcomposeₗ (LinearMap.inr K (W .X) (W' .X))) (B .X))
        (PolynomialVector.mapLinear (postcomposeₗ (LinearMap.inr K (W .Y) (W' .Y))) (B .Y))
        (PolynomialVector.mapLinear (postcomposeₗ (LinearMap.inr K (W .Z) (W' .Z))) (B .Z)) by
    funext c; cases c <;> rfl]
  rw [h, ← hB, show (ofLegs (LinearMap.inr K (W .X) (W' .X)) (LinearMap.inr K (W .Y) (W' .Y))
      (LinearMap.inr K (W .Z) (W' .Z)) : ∀ c, W' c →ₗ[K] W c × W' c) =
      includeRight (K := K) (V := W) (W := W') by funext c; cases c <;> rfl]


/-! ### The free-lunch speedup theorem -/

/-- Distribute a polynomial transformation over a binary splitting of all three map families. -/
private theorem polynomialTransform_ofLegs_add_split
    (PX₁ PX₂ : PolynomialLinearMap K (V .X) (U .X))
    (PY₁ PY₂ : PolynomialLinearMap K (V .Y) (U .Y))
    (PZ₁ PZ₂ : PolynomialLinearMap K (V .Z) (U .Z)) (T : Tensor3 K V) :
    polynomialTransform (ofLegs (PX₁ + PX₂) (PY₁ + PY₂) (PZ₁ + PZ₂)) T =
      polynomialTransform (ofLegs PX₁ PY₁ PZ₁) T + polynomialTransform (ofLegs PX₁ PY₁ PZ₂) T +
        polynomialTransform (ofLegs PX₁ PY₂ PZ₁) T + polynomialTransform (ofLegs PX₁ PY₂ PZ₂) T +
        polynomialTransform (ofLegs PX₂ PY₁ PZ₁) T + polynomialTransform (ofLegs PX₂ PY₁ PZ₂) T +
        polynomialTransform (ofLegs PX₂ PY₂ PZ₁) T +
        polynomialTransform (ofLegs PX₂ PY₂ PZ₂) T := by
  simp only [polynomialTransform_add_maps_X, polynomialTransform_add_maps_Y,
    polynomialTransform_add_maps_Z]
  abel

/-- A path multiplied by `ε^n` has vanishing coefficients in every degree below `n`, so it has
leading coefficient `0` in any prescribed degree `D < n`. -/
private theorem hasLeadingTerm_shift_zero_of_lt {M : Type*} [AddCommMonoid M]
    {n D : ℕ} (Q : PolynomialVector M) (h : D < n) :
    HasLeadingTerm (PolynomialVector.shift n Q) D 0 := by
  refine ⟨?_, fun e he ↦ ?_⟩
  · rw [PolynomialVector.shift_apply, if_neg (by omega)]
  · rw [PolynomialVector.shift_apply, if_neg (by omega)]

/-- **Free-lunch speedup, abstract polynomial form.**

Let `F` and `G` be two polynomial families of leg maps from the source `S` into a common target
leg family, with leading terms `T₁` in degree `d` and `T₂` in degree `d'`.  Assume the three
*mixed* transforms that use `G` on the `Z` leg — but not `G` on all three legs — vanish
identically.  Then `S` degenerates to the sum `T₁ + T₂` with leading degree `2d + d' + 2`.

Proof sketch: apply the family `ε^0 F .X + ε^{d+1} G .X` on the `X` leg, `ε^0 F .Y + ε^{d+1} G .Y`
on the `Y` leg, and `ε^{d+d'+2} F .Z + ε^0 G .Z` on the `Z` leg.  Expanding gives eight blocks.
Three of them (`FFG`, `GFG`, `FGG`) vanish by hypothesis.  The pure block `FFF` is shifted by
`d+d'+2`, so it leads in degree `2d+d'+2`; the pure block `GGG` is shifted by `2d+2`, so it also
leads in degree `2d+d'+2`.  Each of the three remaining junk blocks `GFF`, `FGF`, `GGF` carries a
shift of at least `2d+d'+3`, hence contributes nothing in degree `2d+d'+2` or below.  This is
the single-parameter replacement for the second degeneration parameter `ε` used in
[AlmanLi2026, Corollary 5.1]. -/
theorem polynomialDegeneratesAt_add_of_mixed_eq_zero
    {S : Tensor3 K V} {T₁ T₂ : Tensor3 K U} {d d' : ℕ}
    (F G : ∀ c, PolynomialLinearMap K (V c) (U c))
    (hF : HasLeadingTerm (polynomialTransform F S) d T₁)
    (hG : HasLeadingTerm (polynomialTransform G S) d' T₂)
    (h₁ : polynomialTransform (ofLegs (F .X) (F .Y) (G .Z)) S = 0)
    (h₂ : polynomialTransform (ofLegs (G .X) (F .Y) (G .Z)) S = 0)
    (h₃ : polynomialTransform (ofLegs (F .X) (G .Y) (G .Z)) S = 0) :
    PolynomialDegeneratesAt (2 * d + d' + 2) S (T₁ + T₂) := by
  classical
  have hFeta : ofLegs (F .X) (F .Y) (F .Z) = F := ofLegs_eta F
  have hGeta : ofLegs (G .X) (G .Y) (G .Z) = G := ofLegs_eta G
  refine ⟨ofLegs
      (PolynomialVector.shift 0 (F .X) + PolynomialVector.shift (d + 1) (G .X))
      (PolynomialVector.shift 0 (F .Y) + PolynomialVector.shift (d + 1) (G .Y))
      (PolynomialVector.shift (d + d' + 2) (F .Z) + PolynomialVector.shift 0 (G .Z)), ?_⟩
  rw [polynomialTransform_ofLegs_add_split]
  simp only [polynomialTransform_ofLegs_shift]
  -- The three mixed blocks vanish identically.
  rw [h₁, h₂, h₃, hFeta, hGeta]
  simp only [PolynomialVector.shift_zero]
  -- The surviving blocks.
  have e₁ : HasLeadingTerm
      (PolynomialVector.shift (0 + 0 + (d + d' + 2)) (polynomialTransform F S))
      (2 * d + d' + 2) T₁ := by
    have h := hF.shift (0 + 0 + (d + d' + 2))
    rwa [show 0 + 0 + (d + d' + 2) + d = 2 * d + d' + 2 by omega] at h
  have e₈ : HasLeadingTerm
      (PolynomialVector.shift (d + 1 + (d + 1) + 0) (polynomialTransform G S))
      (2 * d + d' + 2) T₂ := by
    have h := hG.shift (d + 1 + (d + 1) + 0)
    rwa [show d + 1 + (d + 1) + 0 + d' = 2 * d + d' + 2 by omega] at h
  have e₃ : HasLeadingTerm
      (PolynomialVector.shift (0 + (d + 1) + (d + d' + 2))
        (polynomialTransform (ofLegs (F .X) (G .Y) (F .Z)) S)) (2 * d + d' + 2) 0 :=
    hasLeadingTerm_shift_zero_of_lt _ (by omega)
  have e₅ : HasLeadingTerm
      (PolynomialVector.shift (d + 1 + 0 + (d + d' + 2))
        (polynomialTransform (ofLegs (G .X) (F .Y) (F .Z)) S)) (2 * d + d' + 2) 0 :=
    hasLeadingTerm_shift_zero_of_lt _ (by omega)
  have e₇ : HasLeadingTerm
      (PolynomialVector.shift (d + 1 + (d + 1) + (d + d' + 2))
        (polynomialTransform (ofLegs (G .X) (G .Y) (F .Z)) S)) (2 * d + d' + 2) 0 :=
    hasLeadingTerm_shift_zero_of_lt _ (by omega)
  have hz : ∀ n : ℕ, HasLeadingTerm
      (PolynomialVector.shift n (0 : PolynomialTensor K U)) (2 * d + d' + 2) 0 := by
    intro n
    simp
  have := ((((((e₁.add (hz 0)).add e₃).add (hz (0 + (d + 1) + 0))).add e₅).add
    (hz (d + 1 + 0 + 0))).add e₇).add e₈
  simpa using this

/-- **Free-lunch speedup, degeneration form** ([AlmanLi2026], Theorem 5.1 p. 14 and its
bootstrap Corollary 5.1 p. 15).

`A` is a polynomial family of leg maps carrying `S` to `T` with leading degree `d`, and `B` is a
second polynomial family with leading term `T'` in degree `d'`.  Writing both into the block sum
`W c × W' c`, if the three mixed blocks that use the `B`-component on the `Z` leg vanish, then
`S` degenerates to the *direct sum* `T ⊕ T'`. -/
theorem polynomialDegeneratesAt_directSum_of_blockPoly
    {S : Tensor3 K V} {T : Tensor3 K W} {T' : Tensor3 K W'} {d d' : ℕ}
    (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (B : ∀ c, PolynomialLinearMap K (V c) (W' c))
    (hT : HasLeadingTerm (polynomialTransform A S) d T)
    (hT' : HasLeadingTerm (polynomialTransform B S) d' T')
    (h₁ : polynomialTransform
      (ofLegs (V := fun c ↦ PolynomialLinearMap K (V c) (W c × W' c))
        (directSumLeftPolyMaps (K := K) W' A .X)
        (directSumLeftPolyMaps (K := K) W' A .Y)
        (directSumRightPolyMaps (K := K) W B .Z)) S = 0)
    (h₂ : polynomialTransform
      (ofLegs (V := fun c ↦ PolynomialLinearMap K (V c) (W c × W' c))
        (directSumRightPolyMaps (K := K) W B .X)
        (directSumLeftPolyMaps (K := K) W' A .Y)
        (directSumRightPolyMaps (K := K) W B .Z)) S = 0)
    (h₃ : polynomialTransform
      (ofLegs (V := fun c ↦ PolynomialLinearMap K (V c) (W c × W' c))
        (directSumLeftPolyMaps (K := K) W' A .X)
        (directSumRightPolyMaps (K := K) W B .Y)
        (directSumRightPolyMaps (K := K) W B .Z)) S = 0) :
    PolynomialDegeneratesAt (2 * d + d' + 2) S (directSum T T') := by
  have hF : HasLeadingTerm (polynomialTransform (directSumLeftPolyMaps (K := K) W' A) S) d
      (map (includeLeft (K := K) (V := W) (W := W')) T) := by
    rw [polynomialTransform_directSumLeftPolyMaps]
    exact hT.mapLinear _
  have hG : HasLeadingTerm (polynomialTransform (directSumRightPolyMaps (K := K) W B) S) d'
      (map (includeRight (K := K) (V := W) (W := W')) T') := by
    rw [polynomialTransform_directSumRightPolyMaps]
    exact hT'.mapLinear _
  exact polynomialDegeneratesAt_add_of_mixed_eq_zero _ _ hF hG h₁ h₂ h₃

/-- **Free-lunch speedup, abstract restriction form.**

The `d = d' = 0` specialization of `polynomialDegeneratesAt_add_of_mixed_eq_zero` with constant
map families: this is exactly the `diag(1,ε) ⊗ diag(1,ε) ⊗ diag(ε²,1)` monomial degeneration in
the proof of [AlmanLi2026, Theorem 5.1]. -/
theorem polynomialDegeneratesAt_two_add_of_mixed_map_eq_zero
    {S : Tensor3 K V} (f g : ∀ c, V c →ₗ[K] U c)
    (h₁ : map (ofLegs (f .X) (f .Y) (g .Z)) S = 0)
    (h₂ : map (ofLegs (g .X) (f .Y) (g .Z)) S = 0)
    (h₃ : map (ofLegs (f .X) (g .Y) (g .Z)) S = 0) :
    PolynomialDegeneratesAt 2 S (map f S + map g S) := by
  have key : ∀ (h : ∀ c, V c →ₗ[K] U c),
      polynomialTransform (fun c ↦ PolynomialLinearMap.constant (h c)) S =
        PolynomialVector.constant (map h S) := fun h ↦ polynomialTransform_constant h S
  have hmix : ∀ (hx : V .X →ₗ[K] U .X) (hy : V .Y →ₗ[K] U .Y) (hz : V .Z →ₗ[K] U .Z),
      polynomialTransform (ofLegs (PolynomialLinearMap.constant hx)
          (PolynomialLinearMap.constant hy) (PolynomialLinearMap.constant hz)) S =
        PolynomialVector.constant (map (ofLegs hx hy hz) S) := by
    intro hx hy hz
    rw [show (ofLegs (PolynomialLinearMap.constant hx) (PolynomialLinearMap.constant hy)
        (PolynomialLinearMap.constant hz) : ∀ c, PolynomialLinearMap K (V c) (U c)) =
        fun c ↦ PolynomialLinearMap.constant
          (ofLegs (V := fun i ↦ V i →ₗ[K] U i) hx hy hz c) by
      funext c; cases c <;> rfl]
    exact key _
  have hzero : ∀ (hx : V .X →ₗ[K] U .X) (hy : V .Y →ₗ[K] U .Y) (hz : V .Z →ₗ[K] U .Z),
      map (ofLegs hx hy hz) S = 0 →
      polynomialTransform (ofLegs (PolynomialLinearMap.constant hx)
        (PolynomialLinearMap.constant hy) (PolynomialLinearMap.constant hz)) S = 0 := by
    intro hx hy hz h
    rw [hmix, h]
    simp [PolynomialVector.constant, PolynomialVector.monomial]
  have hF : HasLeadingTerm
      (polynomialTransform (fun c ↦ PolynomialLinearMap.constant (f c)) S) 0 (map f S) := by
    rw [key f]
    exact HasLeadingTerm.monomial 0 (map f S)
  have hG : HasLeadingTerm
      (polynomialTransform (fun c ↦ PolynomialLinearMap.constant (g c)) S) 0 (map g S) := by
    rw [key g]
    exact HasLeadingTerm.monomial 0 (map g S)
  have h := polynomialDegeneratesAt_add_of_mixed_eq_zero
    (fun c ↦ PolynomialLinearMap.constant (f c)) (fun c ↦ PolynomialLinearMap.constant (g c))
    hF hG (hzero _ _ _ h₁) (hzero _ _ _ h₂) (hzero _ _ _ h₃)
  simpa using h

/-- **Free-lunch speedup, restriction form** ([AlmanLi2026], Theorem 5.1, p. 14).

Let `f` restrict the source `S` to `T = (f .X ⊗ f .Y ⊗ f .Z) S`, and let `g` be a second family
of leg maps with target legs `W'`.  Post-compose `f` with the left inclusions and `g` with the
right inclusions of the block sum `W c × W' c`.  If the three mixed blocks
`(FL, FL, GR)`, `(GR, FL, GR)`, `(FL, GR, GR)` annihilate `S`, then `S` degenerates, at leading
degree `2`, to the direct sum `T ⊕ T'` with `T' = (g .X ⊗ g .Y ⊗ g .Z) S`.

The paper takes `g` to be the *maximal* family with these properties (the annihilators `A'` and
`B'` of its Theorem 5.1); the degeneration itself works for any such `g`. -/
theorem polynomialDegeneratesAt_two_directSum_of_mixed_map_eq_zero
    {S : Tensor3 K V} (f : ∀ c, V c →ₗ[K] W c) (g : ∀ c, V c →ₗ[K] W' c)
    (h₁ : map (ofLegs (V := fun c ↦ V c →ₗ[K] W c × W' c)
      (directSumLeftMaps (K := K) W' f .X)
      (directSumLeftMaps (K := K) W' f .Y) (directSumRightMaps (K := K) W g .Z)) S = 0)
    (h₂ : map (ofLegs (V := fun c ↦ V c →ₗ[K] W c × W' c)
      (directSumRightMaps (K := K) W g .X)
      (directSumLeftMaps (K := K) W' f .Y) (directSumRightMaps (K := K) W g .Z)) S = 0)
    (h₃ : map (ofLegs (V := fun c ↦ V c →ₗ[K] W c × W' c)
      (directSumLeftMaps (K := K) W' f .X)
      (directSumRightMaps (K := K) W g .Y) (directSumRightMaps (K := K) W g .Z)) S = 0) :
    PolynomialDegeneratesAt 2 S (directSum (map f S) (map g S)) := by
  have hL : map (directSumLeftMaps (K := K) W' f) S =
      map (includeLeft (K := K) (V := W) (W := W')) (map f S) := by
    rw [show (directSumLeftMaps (K := K) W' f) =
        fun c ↦ (includeLeft (K := K) (V := W) (W := W') c) ∘ₗ f c from rfl, map_comp]
    rfl
  have hR : map (directSumRightMaps (K := K) W g) S =
      map (includeRight (K := K) (V := W) (W := W')) (map g S) := by
    rw [show (directSumRightMaps (K := K) W g) =
        fun c ↦ (includeRight (K := K) (V := W) (W := W') c) ∘ₗ g c from rfl, map_comp]
    rfl
  have h := polynomialDegeneratesAt_two_add_of_mixed_map_eq_zero
    (directSumLeftMaps (K := K) W' f) (directSumRightMaps (K := K) W g) h₁ h₂ h₃
  rw [hL, hR] at h
  exact h

/-- Degree-forgetting form of the restriction free-lunch speedup theorem. -/
theorem polynomialDegenerates_directSum_of_mixed_map_eq_zero
    {S : Tensor3 K V} (f : ∀ c, V c →ₗ[K] W c) (g : ∀ c, V c →ₗ[K] W' c)
    (h₁ : map (ofLegs (V := fun c ↦ V c →ₗ[K] W c × W' c)
      (directSumLeftMaps (K := K) W' f .X)
      (directSumLeftMaps (K := K) W' f .Y) (directSumRightMaps (K := K) W g .Z)) S = 0)
    (h₂ : map (ofLegs (V := fun c ↦ V c →ₗ[K] W c × W' c)
      (directSumRightMaps (K := K) W g .X)
      (directSumLeftMaps (K := K) W' f .Y) (directSumRightMaps (K := K) W g .Z)) S = 0)
    (h₃ : map (ofLegs (V := fun c ↦ V c →ₗ[K] W c × W' c)
      (directSumLeftMaps (K := K) W' f .X)
      (directSumRightMaps (K := K) W g .Y) (directSumRightMaps (K := K) W g .Z)) S = 0) :
    PolynomialDegenerates S (directSum (map f S) (map g S)) :=
  (polynomialDegeneratesAt_two_directSum_of_mixed_map_eq_zero f g h₁ h₂ h₃).toPolynomialDegenerates

/-! ### A minimal regression client

DESIGN.md asks every major semantic operation to carry a deliberately tiny client that catches
relation-direction, leg, and block-association errors.  Here it is: the two-dimensional diagonal
tensor `⟨2⟩` with the two coordinate projections as `f` and `g`.  All three mixed blocks vanish,
and the free-lunch theorem returns the split `⟨1⟩ ⊕ ⟨1⟩`.
-/

section RegressionClient

variable (K)

/-- Two-dimensional coordinate space on each leg of the smoke-test tensor. -/
private abbrev TestSpace : Leg → Type u := fun _ ↦ K × K

/-- The diagonal tensor `⟨2⟩ = e₁ ⊗ e₁ ⊗ e₁ + e₂ ⊗ e₂ ⊗ e₂` on two-dimensional legs. -/
private noncomputable def testDiagonalTwo : Tensor3 K (TestSpace K) :=
  pure (K := K) (ofLegs (V := TestSpace K) (1, 0) (1, 0) (1, 0)) +
    pure (K := K) (ofLegs (V := TestSpace K) (0, 1) (0, 1) (0, 1))

/-- Legwise images of a pure test tensor. -/
private theorem testPure_map (FX FY FZ : (K × K) →ₗ[K] (K × K)) (a b c : K × K) :
    map (ofLegs (V := fun _ : Leg ↦ (K × K) →ₗ[K] (K × K)) FX FY FZ)
        (pure (K := K) (ofLegs (V := TestSpace K) a b c)) =
      pure (K := K) (ofLegs (V := TestSpace K) (FX a) (FY b) (FZ c)) := by
  rw [map_pure]
  congr 1
  funext i
  cases i <;> rfl

/-- A sum of two pure test tensors vanishes as soon as each summand has a zero leg. -/
private theorem testPure_add_eq_zero {a b c a' b' c' : K × K} (i j : Leg)
    (h : ofLegs (V := TestSpace K) a b c i = 0)
    (h' : ofLegs (V := TestSpace K) a' b' c' j = 0) :
    pure (K := K) (ofLegs (V := TestSpace K) a b c) +
      pure (K := K) (ofLegs (V := TestSpace K) a' b' c') = 0 := by
  have hz : pure (K := K) (ofLegs (V := TestSpace K) a b c) = 0 :=
    (PiTensorProduct.tprod K).map_coord_zero i h
  have hz' : pure (K := K) (ofLegs (V := TestSpace K) a' b' c') = 0 :=
    (PiTensorProduct.tprod K).map_coord_zero j h'
  rw [hz, hz', add_zero]

/-- **Smoke test.**  Applying the free-lunch speedup theorem to `⟨2⟩` with the two coordinate
projections splits it as a direct sum of the two one-dimensional diagonal blocks. -/
private theorem testDiagonalTwo_freeLunch :
    PolynomialDegeneratesAt 2 (testDiagonalTwo K)
      (directSum (map (fun _ : Leg ↦ LinearMap.fst K K K) (testDiagonalTwo K))
        (map (fun _ : Leg ↦ LinearMap.snd K K K) (testDiagonalTwo K))) := by
  refine polynomialDegeneratesAt_two_directSum_of_mixed_map_eq_zero
    (W' := fun _ ↦ K) (fun _ ↦ LinearMap.fst K K K) (fun _ ↦ LinearMap.snd K K K) ?_ ?_ ?_
  · simp only [testDiagonalTwo, map_add, directSumLeftMaps, directSumRightMaps, testPure_map]
    refine testPure_add_eq_zero (K := K) Leg.Z Leg.X ?_ ?_ <;> rfl
  · simp only [testDiagonalTwo, map_add, directSumLeftMaps, directSumRightMaps, testPure_map]
    refine testPure_add_eq_zero (K := K) Leg.X Leg.Y ?_ ?_ <;> rfl
  · simp only [testDiagonalTwo, map_add, directSumLeftMaps, directSumRightMaps, testPure_map]
    refine testPure_add_eq_zero (K := K) Leg.Y Leg.X ?_ ?_ <;> rfl

end RegressionClient

end AlgebraicComplexity.Tensor
