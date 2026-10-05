/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Leg

/-!
# Definition-only standard coordinate spaces

This lightweight module names the function spaces used for concrete tensor coordinates without
loading tensor products, bases, or coordinate equivalences.  `Tensor/Coordinates.lean` re-exports
the same declaration and supplies the full basis-dependent bridge.

The separation lets the matrix-multiplication tensor itself remain a small finite sum of standard
basis pure tensors; only clients that inspect coefficients pay for the coordinate-basis API.
-/

namespace AlgebraicComplexity.Tensor

universe u w

/-- Coordinate vector spaces on a family of finite index types. -/
abbrev CoordinateSpace (K : Type u) (κ : Leg → Type w) (i : Leg) := κ i → K

end AlgebraicComplexity.Tensor
