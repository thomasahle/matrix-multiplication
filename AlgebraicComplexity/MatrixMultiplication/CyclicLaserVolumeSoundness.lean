/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CyclicLaserRateSoundness
import AlgebraicComplexity.MatrixMultiplication.CyclicLaserVolume

/-!
# Soundness of cyclic laser volume sequences

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  The generic cyclic-rate soundness and
value bridge live in `CyclicLaserRateSoundness.lean`; the finite subexponential sequence producer
lives in `CyclicLaserVolume.lean`.  This compatibility/client module imports both old halves and
composes them into the numerical `omega` bound used by volume-sequence clients.

Keeping the old filename as this facade preserves every existing import path while letting clients
that need only the cyclic rate or its soundness avoid the subexponential-growth dependency cone.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

section Field

variable (K : Type u) [Field K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **From finite cyclic certificate data to a numerical bound on `omega`.**  A
`SubexponentialCyclicLaserVolumeSequence` — finite extractions at every proportional repetition,
with a certified subexponential copy-count loss — together with a border-rank certificate
`R̲(T) ≤ b` and a growing volume base bounds the matrix-multiplication exponent by

```text
omega ≤ 3 * (3 * stride * log b - log copyBase) / log volumeBase.
```

Proof sketch: `SubexponentialCyclicLaserVolumeSequence.hasCyclicLaserExtractionRate` absorbs the
subexponential loss and yields the cyclic rate in exactly the coordinates
`HasCyclicLaserExtractionRate.omega_le_of_borderRank_le` consumes. -/
theorem SubexponentialCyclicLaserVolumeSequence.omega_le_of_borderRank_le
    {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase : ℝ} {b : ℕ}
    (h : SubexponentialCyclicLaserVolumeSequence K T stride copyBase volumeBase)
    (hb : 0 < b) (hle : borderRank T ≤ b) (hvolume : 0 < Real.log volumeBase) :
    omega K ≤
      3 * (3 * (stride : ℝ) * Real.log b - Real.log copyBase) / Real.log volumeBase :=
  HasCyclicLaserExtractionRate.omega_le_of_borderRank_le K
    h.hasCyclicLaserExtractionRate h.stride_pos hb hle hvolume

end Field

end AlgebraicComplexity
