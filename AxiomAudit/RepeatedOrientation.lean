/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.RepeatedOrientation

set_option autoImplicit false

/-!
# Axiom audit for the repeated-orientation degeneration count

Focused trust audit for the general form of the six-fold repeated `xzy` orientation count in
`MatrixMultiplication/RepeatedOrientation.lean`, the level-two degeneration-system bookkeeping of
[duan2023faster].

`AxiomAudit.lean:282-284` asserts the downstream published-weight forms
`six_repeated_xzy_of_published_weights`,
`constituent_six_repeated_xzy_of_published_termWeights` and `arbitrary_orientations`.  The
general theorem they instantiate carries no assertion of its own; it is asserted here.
-/

namespace MatrixMultiplication.DegenerationSystem

#assert_axioms six_repeated_xzy

end MatrixMultiplication.DegenerationSystem
