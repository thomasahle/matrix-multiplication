/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TauValueCore
import AlgebraicComplexity.MatrixMultiplication.TauValueCalculus
import AlgebraicComplexity.MatrixMultiplication.TauValueDirectSum
import AlgebraicComplexity.MatrixMultiplication.TauValueIndexedDirectSum
import AlgebraicComplexity.MatrixMultiplication.TauValueSuperadditivity
import AlgebraicComplexity.MatrixMultiplication.TauValueSoundness
import AlgebraicComplexity.MatrixMultiplication.TauValueCyclicSoundness

/-!
# The complete Coppersmith--Winograd τ-value API

Compatibility umbrella re-exporting every dependency tier of the value formalism:

* `TauValueCore.lean` contains finite extraction certificates and their elementary calculus;
* `TauValueCalculus.lean`, `TauValueDirectSum.lean`, and `TauValueSuperadditivity.lean` prove the
  product, unrestricted power, and direct-sum laws;
* `TauValueIndexedDirectSum.lean` assembles already separated finite families;
* `TauValueSoundness.lean` connects ordinary certificates to asymptotic rank and `omega` through
  Schönhage's asymptotic sum inequality;
* `TauValueCyclicSoundness.lean` adapts symmetrized cyclic certificates to that theorem.

New clients should import the narrowest leaf above. Existing users may continue importing this
umbrella without losing any public law that lived in the pre-split module.
-/
