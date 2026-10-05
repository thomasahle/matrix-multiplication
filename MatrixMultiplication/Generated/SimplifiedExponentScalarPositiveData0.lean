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

namespace MatrixMultiplication.Generated.SimplifiedExponentScalar.Positive0

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    3, 5, 7, 9, 11, 13,
    15, 17, 19, 21, 23, 25,
    27, 29, 31, 33, 35, 37,
    39, 41, 43, 45, 47, 49,
    51, 53, 55, 57, 59, 61,
    63, 65, 67, 69, 71, 73,
    75, 77, 79, 81, 83, 85,
    87, 89, 91, 93, 95, 97,
    99, 101, 103, 105, 107, 109,
    111, 113, 115, 117, 119, 121,
    123, 125, 127
  ]

def coefficients : Array ℕ := #[
    229450765983714804928100903725243, 1872075277624321954399374875708898, 1217580170230317869069827628322314, 2647288987907088872824423033470995, 27744998638299695926140503493002, 474533569417405996222249586220624,
    606769864709679746421421411786666, 904305867392646201542309932476619, 1079647779892855253821027998244849, 511547085086638367985299294460011, 93443541948263582647886525317814, 569035765099117035314443870329888,
    437744531620749881232651445264374, 1435992435268278047946464138495672, 839558375407983024357423228701866, 344701108850963627485558151008930, 765756914182788726609839875930261, 563641316625175227045133527922392,
    119812701251791731968528654391793, 928678334217560415763896226147050, 1408649644108488546028537855775394, 353987436836944442483728377700716, 302689920631088999585158068122812, 215273840957266333853655059272947,
    1406632758822530737590652732583060, 753247569890400372199653054299898, 1122549365419528107433366161220858, 634714544557736899824147988061297, 1581115648171216914069687578016497, 855993192103785963342503582346640,
    117352838908607356813632221549806, 437616008290791461838806019589906, 1024772396584018085285303239698815, 476698355873156939953837628990027, 1031648687305981662894564627948386, 2243506532766880816522981858529235,
    354044016410947157918354956543555, 1958139187284852584274804618275038, 269100505011354735163356643533881, 2180695462043235157895959527664106, 404270025637048079780415712006923, 436194516305297509259834176660862,
    248659336711131006148138515800362, 263167352539282748994334199883308, 193730962607432880984504750833650, 313066763406941657385043597821920, 26470140838534655222093683876973, 279177137196537599320238118238710,
    488446670491169076311778874966419, 340371683710545292501269395902176, 402878537035237269933531896733344, 475745781874266552540688401779156, 522696662597808763618035165311032, 404312514952533791500251587804826,
    1131769435251530923617562885779918, 225875136544437634266108632670855, 1590334244274323219141189422426656, 577276972335114052848378356241116, 1118583501479742456066597030104241, 625109542350914420263836846457147,
    78709479803185926713250832382523, 1600739809924851644090516258288776, 2375439050490215501315365752635458
  ]

def scales : Array ℕ := #[
    1, 2, 2, 3, 3, 3,
    3, 4, 4, 4, 4, 4,
    4, 4, 4, 5, 5, 5,
    5, 5, 5, 5, 5, 5,
    5, 5, 5, 5, 5, 5,
    5, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6,
    6, 6, 6
  ]

abbrev Term := Fin 63
def argument (term : Term) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : Term) : ℕ := coefficients[term.val]?.getD 0
def scale (term : Term) : ℕ := scales[term.val]?.getD 0

theorem arguments_pos : ∀ term, 0 < argument term := by decide
theorem scales_valid : ∀ term, 2 ^ scale term ≤ argument term := by decide

noncomputable def exact : ℝ := logSum 112 argument coefficient
noncomputable def fastLower : ℝ :=
  fastLogSumLowerWithScale 7 112 argument coefficient scale
noncomputable def floor : ℝ := 25988176921133 / 500000000000

theorem floor_le_fast : floor ≤ fastLower := by
  norm_num [floor, fastLower, fastLogSumLowerWithScale, fastLogSumUpperWithScale,
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

theorem exact_bound : floor ≤ exact := by
  exact floor_le_fast.trans (fastLogSumLowerWithScale_le_logSum 7 112 argument coefficient scale scales_valid)

end MatrixMultiplication.Generated.SimplifiedExponentScalar.Positive0
