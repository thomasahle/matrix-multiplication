import MatrixMultiplication.Generated.LevelFourTopRaw0
import MatrixMultiplication.Generated.LevelFourTopRaw1
import MatrixMultiplication.Generated.LevelFourTopRaw2
import MatrixMultiplication.Generated.LevelFourTopRaw3
import MatrixMultiplication.Generated.LevelFourTopRaw4
import MatrixMultiplication.Generated.LevelFourTopRaw5

/-!
# Generated exact joint top-mass data

Source SHA-256: `7a255f50ab903cb7f3da56d93ceccfff3acf39061463115655d7f3f63e746481`.

The arrays are emitted from the archived `2^32`-denominator certificate.  Generated checking
modules use Lean's kernel with `decide`; no floating-point values are imported.
The large rows live in independent root modules so exact row checks have a bounded memory
footprint.
-/

namespace MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top

def zeroNumerators : Array (Array ℕ) :=
  #[zeroNumerators0, zeroNumerators1, zeroNumerators2, zeroNumerators3, zeroNumerators4, zeroNumerators5]

def branchNumerators : Array (Array (Array ℕ)) :=
  #[branchNumerators0, branchNumerators1, branchNumerators2, branchNumerators3, branchNumerators4, branchNumerators5]

/-- The exact joint top mass from the SHA-pinned certificate. -/
def certificate : TopMassArrays where
  zero := zeroNumerators
  branch := branchNumerators

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
