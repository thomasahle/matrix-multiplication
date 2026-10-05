/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Q20EndpointAdapter

set_option autoImplicit false

/-!
# Axiom audit for the q20 endpoint adapter

Every declaration of `MatrixMultiplication/Q20EndpointAdapter.lean` -- the six exact q20
constants, the numerical stage record with its constructor and projections, the derived copy
and volume bases, the exact rational lemmas including the backed-off margin identity, the
tail-native endpoints, the exact-sequence convenience corollary, and the cyclic q20 endpoint
-- is asserted to depend on no axiom outside `propext`,
`Classical.choice`, and `Quot.sound`.

The audit says nothing about whether any of the endpoints' data hypotheses can be discharged:
they are open obligations, constructed nowhere in this repository.  An audited
conditional theorem is still conditional.  The generic cyclic budget the last endpoint
applies is asserted in its own companion,
`AxiomAudit/CoppersmithWinogradCyclicVolumeEndpoint.lean`.

## References

The audited module transcribes `prop:tail-native-cw-endpoint`,
`better_bound/paper.tex:2199-2231` (the CW endpoint from a stage family), and the strict
form of the final assembly `cor:repeated-volume`, `better_bound/paper.tex:2255-2266`, at
`q = 5` and `power = 8`.  Its source construction and value calculus are
`[coppersmith1990matrix]`; the soundness direction is `[schonhage1981partial]`; the laser /
total-weight lineage the manuscript extends is `[duan2023faster]` and `[alman2025more]`.
-/

open MatrixMultiplication.Q20EndpointAdapter

#assert_axioms q20RetainedFloor
#assert_axioms q20VolumeFloor
#assert_axioms q20SourceCostUpper
#assert_axioms q20Target
#assert_axioms q20TargetMargin
#assert_axioms q20BackedOffVolume
#assert_axioms q20Target_eq_decimal
#assert_axioms q20Target_nonneg
#assert_axioms q20RetainedFloor_pos
#assert_axioms q20VolumeFloor_pos
#assert_axioms q20TargetMargin_pos
#assert_axioms q20TargetMargin_eq
#assert_axioms q20_directed_ratio_lt_target
#assert_axioms q20BackedOffVolume_pos
#assert_axioms q20BackedOffVolume_lt_q20VolumeFloor
#assert_axioms q20_backedOff_margin_eq
#assert_axioms rankBudgetUpper_lt_q20SourceCostUpper
#assert_axioms Q20StageBases
#assert_axioms Q20StageBases.mk
#assert_axioms Q20StageBases.stride
#assert_axioms Q20StageBases.retained
#assert_axioms Q20StageBases.volume
#assert_axioms Q20StageBases.stride_pos
#assert_axioms Q20StageBases.retained_floor
#assert_axioms Q20StageBases.volume_floor
#assert_axioms Q20StageBases.copyBase
#assert_axioms Q20StageBases.volumeBase
#assert_axioms q20StageBases
#assert_axioms q20StageBases_spec
#assert_axioms q20StageBases_copyBase
#assert_axioms q20StageBases_volumeBase
#assert_axioms sourceBudget_lt_q20_backedOff_endpoint
#assert_axioms omega_lt_236999_of_q20EventualStages
#assert_axioms omega_lt_236999_of_q20EventualStages_at_floor
#assert_axioms omega_lt_236999_of_q20VolumeSequence
#assert_axioms omega_lt_236999_of_q20VolumeSequence_at_floor
#assert_axioms omega_lt_236999_of_q20CyclicStages
