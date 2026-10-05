import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

/-! **PROVENANCE QUARANTINE — R7, 2026-08-28 (eab2c7 retained side).**  The retained exponent
`8.200434` this payload feeds is computed from the **ARCHIVED (uncorrected)** evaluator
complement table.  Under the corrected table the same certificate yields `8.160594`, which is
below the `8.2` floor, so the payload was **refuted for endpoint use on 2026-08-28** (commit
`8a8e110`'s analysis).  Every declaration below stays kernel-true *as a statement about the
emitted arrays*; none of it may instantiate an `hsemantic` obligation or any retained-exponent
endpoint.  Listed in `scripts/artifact_provenance_quarantine.txt` and enforced by
`scripts/check_artifact_provenance.sh`.
-/

namespace MatrixMultiplication.Generated.SimplifiedExponentScalar.Negative0

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    129, 131, 133, 135, 137, 139,
    141, 143, 145, 147, 149, 151,
    153, 155, 157, 159, 161, 163,
    165, 167, 169, 171, 173, 175,
    177, 179, 181, 183, 185, 187,
    189, 191, 193, 195, 197, 199,
    201, 203, 205, 207, 209, 211,
    213, 215, 217, 219, 221, 223,
    225, 227, 229, 231, 233, 235,
    237, 239, 241, 243, 245, 247,
    249, 251, 253, 255
  ]

def coefficients : Array ℕ := #[
    1182180261811493532396744871713362, 346600259011079753221877593694663, 342489176058461528119446661319187, 338526775241081502226297904087331, 5546178908788645165507709964864297, 342293345361334170850373638228992,
    885227437391550866010432563677957, 651074257369357704682618413085114, 1358834774303528986209999033579639, 297889659910764807263474544460914, 320892551966795027047888637307850, 856948462887431476299776591714954,
    664862125542572198726680197216583, 98427966839110966128919281092102, 1087583386515415557898972842895360, 446491819664265954966544941882786, 3943201159410742753221411554876208, 2184664926492021017387233090229673,
    1018058642030587078543396262284178, 1006330820226618240926061127498150, 635990329277185598235149198794420, 764967349541071827932413522450531, 428182792907841260344587609920467, 1744959451063579295693386424398922,
    205434273564223354632589114460160, 1605651013603637955023259760782435, 72529978724719286811715783066497, 751479658192135378102031258847890, 275919107256100903291175460904960, 327098968714803420286513702305747,
    403759986909154656504515698731983, 504362341967690528007721008523314, 723104515850447188039424100236288, 694858004788137602351958902684878, 695179546254090851534668691685611, 191421319618513167554110692543750,
    653730575513735790233526542110836, 531873168410406691316270002336768, 668683245370529584674968173674263, 36843149385267220998418302001644, 337633979674682354739727338308382, 189704176522003973130484477586679,
    889080136136990709770499988811491, 1549378218168682942448194077989651, 787825293119899734355762378501113, 400771985465187452828968878175802, 367683443822121931455143492985048, 93531238290439419660329960404001,
    99661747903393806816743890868202, 588066119295019825840943335169226, 21000816880447721046714820415360, 1542836138743425120541747525652480, 144985704837517786757944035143616, 101237154241130660999097308240709,
    2590617307571194615982979829721692, 438549443141677790042066125364130, 852232331796646872470262201110737, 2357942135713051611781277475261137, 1117385919827049030866917180607443, 2996945952273180936925755806737607,
    4324739465943667898016362712235008, 681459198041399465056606367963354, 124023137721400512929030742559216, 1724754626869490669108180472775524
  ]

def scales : Array ℕ := #[
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7
  ]

abbrev Term := Fin 64
def argument (term : Term) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : Term) : ℕ := coefficients[term.val]?.getD 0
def scale (term : Term) : ℕ := scales[term.val]?.getD 0

theorem arguments_pos : ∀ term, 0 < argument term := by decide
theorem scales_valid : ∀ term, 2 ^ scale term ≤ argument term := by decide

noncomputable def exact : ℝ := logSum 112 argument coefficient
noncomputable def fastUpper : ℝ :=
  fastLogSumUpperWithScale 7 112 argument coefficient scale
noncomputable def ceiling : ℝ := 43060598172751 / 500000000000

theorem fast_le_ceiling : fastUpper ≤ ceiling := by
  norm_num [ceiling, fastUpper, fastLogSumLowerWithScale, fastLogSumUpperWithScale,
    argument, coefficient, scale, arguments, coefficients, scales,
    MatrixMultiplication.FastDyadicLog.numeratorLogLower,
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper,
    MatrixMultiplication.FastDyadicLog.fastLogTwoLower,
    MatrixMultiplication.FastDyadicLog.fastLogTwoUpper,
    reducedArgument,
    AlgebraicComplexity.Analysis.logRatioLower,
    AlgebraicComplexity.Analysis.logRatioUpper,
    AlgebraicComplexity.Analysis.atanhPartial,
    AlgebraicComplexity.Analysis.atanhRemainder, Fin.sum_univ_succ,
    Finset.sum_range_succ, mass]

theorem exact_bound : exact ≤ ceiling := by
  exact (logSum_le_fastLogSumUpperWithScale 7 112 argument coefficient scale scales_valid).trans fast_le_ceiling

end MatrixMultiplication.Generated.SimplifiedExponentScalar.Negative0
