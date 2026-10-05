/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.AsymmetricLaserCWBaseProduct
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteOrientation

/-!
# Finite product admission for the DWZ 022 middle split

This literal client of [duan2023faster] follows `papers/sources/2210.10173/`:
`prelim.tex:294-309` supplies the ordered child pair, `second_power.tex:51-63` supplies
the native base matrix components, and `component_value.tex:205-225` retains both
complementary occurrences. The committed prefix and references are admitted by the shared
finite product rule. Two native 011 occurrences derive MM(1,1,36) at q = 6.
A separate pair with both children in the zero-X frame derives MM(1,36,1), in the
actual whole-pair permuted source via the existing external-product permutation law.

These are two frames of one split-term product, not extraction of the entire 022 component
or new root factors. Old identity references remain unchanged. Profile transport, equality
of shared restriction maps, producing-DAG Checks, repair and the endpoint remain open.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor AsymmetricLaserData MoreAsymmetryCompatibility

universe u

/-- The literal finite prefix and both labelled native 011 references of the 022 middle split. -/
def dwz63Row022ProductData : CWBaseProductData :=
  { q := dwz63Q, shapePrefix := dwz63Row022ChildShapes, children := dwz63Row022MiddleChildren }

/-- Both actual native child references pass the shared finite product checker. -/
theorem dwz63Row022Product_checked : cwBaseProductCheck dwz63Row022ProductData = true := rfl

/-- The finite product checker derives the native paired-011 restriction at q = 6. -/
theorem dwz63Row022Product_restricts (K : Type u) [CommRing K] :
    Restricts
      (Tensor.external
        (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩)
        (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩))
      (matrixMultiplication (K := K) 1 1 36) := by
  obtain ⟨left, right, hl, hr, _, _, hrest⟩ :=
    cwBaseProductCheck_sound K dwz63Row022ProductData dwz63Row022Product_checked
  change some ((⟨cw011, by decide⟩ : cwBlockSupport), Equiv.refl Leg) = some left at hl
  change some ((⟨cw011, by decide⟩ : cwBlockSupport), Equiv.refl Leg) = some right at hr
  have el := Option.some.inj hl
  have er := Option.some.inj hr
  subst left
  subst right
  change Restricts
    (Tensor.external
      (Tensor.permute (Equiv.refl Leg) (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩))
      (Tensor.permute (Equiv.refl Leg) (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩)))
    (matrixMultiplication (K := K) 1 1 36) at hrest
  let T := cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩
  exact ((Isomorphic.cancel_permute_refl T).symm.external
    (Isomorphic.cancel_permute_refl T).symm).restricts.trans hrest

/-- A separate product with both labelled occurrences carrying the actual zero-X011 frame. -/
def dwz63Row022RotatedProductData : CWBaseProductData :=
  { dwz63Row022ProductData with
    children := { left := dwz63ZeroX011Child, right := dwz63ZeroX011Child } }

/-- Both rotated child occurrences pass native admission and inverse-frame decoding. -/
theorem dwz63Row022RotatedProduct_checked :
    cwBaseProductCheck dwz63Row022RotatedProductData = true := rfl

/-- Apply finite admission in the actual whole-pair zero-X frame; no map equality is asserted. -/
theorem dwz63Row022RotatedProduct_restricts (K : Type u) [CommRing K] :
    Restricts
      (Tensor.permute (zeroOrientation .X)
        (Tensor.external
          (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩)
          (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩)))
      (matrixMultiplication (K := K) 1 36 1) := by
  obtain ⟨left, right, hl, hr, _, _, hrest⟩ :=
    cwBaseProductCheck_sound K dwz63Row022RotatedProductData
      dwz63Row022RotatedProduct_checked
  change some ((⟨cw011, by decide⟩ : cwBlockSupport), zeroOrientation .X) = some left at hl
  change some ((⟨cw011, by decide⟩ : cwBlockSupport), zeroOrientation .X) = some right at hr
  have el := Option.some.inj hl
  have er := Option.some.inj hr
  subst left
  subst right
  change Restricts
    (Tensor.external
      (Tensor.permute (zeroOrientation .X) (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩))
      (Tensor.permute (zeroOrientation .X)
        (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩)))
    (matrixMultiplication (K := K) 1 36 1) at hrest
  simpa only [Tensor.permute_external] using hrest

end AlgebraicComplexity.Examples
