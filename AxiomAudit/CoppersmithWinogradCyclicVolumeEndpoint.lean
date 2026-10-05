/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradCyclicVolumeEndpoint

set_option autoImplicit false

/-!
# Axiom audit for the cyclic CW volume endpoint

The module's single declaration, the cyclic source-budget theorem, is asserted to depend on no
axiom outside `propext`, `Classical.choice`, and `Quot.sound`.

The audit says nothing about whether the theorem's cyclic sequence hypothesis can be discharged:
constructing one is an open (Mode-B) obligation.  An audited conditional theorem is still
conditional.

## References

The audited module transcribes the three-source accounting of `lem:volume`,
`better_bound/paper.tex:2160-2181`, on the Coppersmith--Winograd source of
`[coppersmith1990matrix]`; its soundness direction is the asymptotic sum inequality of
`[schonhage1981partial]`.
-/

open AlgebraicComplexity.Examples

#assert_axioms retained_add_omega_mul_volume_le_cwPowerBudget_of_cyclicSequence
