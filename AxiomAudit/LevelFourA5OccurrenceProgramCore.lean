/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.LevelFourA5OccurrenceProgramCore

set_option autoImplicit false

/-!
# Axiom audit for the lightweight level-four A5 program constructor

## References

- [coppersmith1990matrix] Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via
  Arithmetic Progressions*.
- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

#assert_axioms MatrixMultiplication.LevelFourA5OccurrenceProgram.nonempty_levelFourValidSlot_of_parentMass_pos
#assert_axioms MatrixMultiplication.LevelFourA5OccurrenceProgram.cwLevelFourOccurrenceA5Program
#assert_axioms MatrixMultiplication.LevelFourA5OccurrenceProgram.cwLevelFourOccurrenceA5Program_stateProfile
