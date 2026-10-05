import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 8, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 4488926448340530245875439501312
def positiveArguments : Array ℕ := #[
    9, 12582943, 12582881, 45216637, 80615605, 45210393,
    99495, 122645369, 122645313, 1591859, 103135, 3548371,
    43025397, 887107, 106317
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 237685073116236888616638349312, 237683901969349136944625352704, 427059062073766931892958920704, 1522785724193034340149829304320, 427000089161128855763530285056,
    30070518605639382434347745280, 1158352759689559632265659547648, 1158352230784513550865395613696, 30069366348217562240915603456, 974082534421521718229073920, 33513416558373291713135378432,
    406363385409920369136840474624, 33513954908152338852689739776, 1004135674718504140369035264
  ]
def positiveScales : Array ℕ := #[
    3, 23, 23, 25, 26, 25,
    16, 26, 26, 20, 16, 21,
    25, 19, 16
  ]
def negativeArguments : Array ℕ := #[
    432580619943, 14882983195103, 180462039582001, 14883222270759, 222963479441, 2399896287945,
    369705326114515, 369705156774595, 4799608850851, 2399896287945, 34218230266575, 9598155971085,
    432580619943, 432578466137, 432578466137, 14882910162465, 180461149895375, 14883149237465,
    222962338927, 34218230266575, 164786018022987, 659143771669681, 34216918321527, 369705326114515,
    164786018022987, 369654376814293, 14882983195103, 14882910162465, 9598155971085, 369654376814293,
    369654207474651, 9597788545859, 369705156774595, 659143771669681, 369654207474651, 180462039582001,
    180461149895375, 4799608850851, 34216918321527, 9597788545859, 14883222270759, 14883149237465,
    222963479441, 222962338927, 3, 15, 15, 3
  ]
def negativeCoefficients : Array ℕ := #[
    243521239847874118828425216, 8378374696453403096054235136, 101591096777002425416325005312, 8378509284082812465665015808, 251034560731929211446493184, 2702043007029234642903367680,
    104062798057888591111876771840, 104062750392938552927526584320, 2701939579027087264172736512, 2702043007029234642903367680, 9631575567364062375523123200, 2701640728426394198747381760,
    243521239847874118828425216, 243520027362886740286111744, 243520027362886740286111744, 8378333582733242760513454080, 101590595927957759152095232000, 8378468169993356960679854080,
    251033276627322858738024448, 9631575567364062375523123200, 371065124682096045579646795776, 371064955559394831204689641472, 9631206287662230915055091712, 104062798057888591111876771840,
    371065124682096045579646795776, 104048457104795179441306206208, 8378374696453403096054235136, 8378333582733242760513454080, 2701640728426394198747381760, 104048457104795179441306206208,
    104048409439923391300481581056, 2701537307419462941229973504, 104062750392938552927526584320, 371064955559394831204689641472, 104048409439923391300481581056, 101591096777002425416325005312,
    101590595927957759152095232000, 2701939579027087264172736512, 9631206287662230915055091712, 2701537307419462941229973504, 8378509284082812465665015808, 8378468169993356960679854080,
    251034560731929211446493184, 251033276627322858738024448, 475368975085586025561263702016, 2376844875427930127806318510080, 2376844875427930127806318510080, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    38, 43, 47, 43, 37, 41,
    48, 48, 42, 41, 44, 43,
    38, 38, 38, 43, 47, 43,
    37, 44, 47, 49, 44, 48,
    47, 48, 43, 43, 43, 48,
    48, 43, 48, 49, 48, 47,
    47, 42, 44, 43, 43, 43,
    37, 37, 1, 3, 3, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 23584966055024664, 23584958946408428, 25430350359444620, 26264555796724007, 25430151122825887,
    16602336406145524, 26869917518750647, 26869916860014479, 20602281123164197, 16654174484712247, 21758725427840936,
    25358685168441891, 19758748602688442, 16698012775485564
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38654178076309660, 43758728967875397, 47358688724724612, 43758752142697981, 37698016465436760, 41126109199440302,
    48393369156107414, 48393368495294866, 42126053975329776, 41126109199440302, 44959830392809637, 43125894395845251,
    38654178076309660, 38654170893156209, 38654170893156209, 43758721888375110, 47358681612150409, 43758745063247826,
    37698009085671665, 44959830392809637, 47227587164483933, 49227586506937531, 44959775078046910, 48393369156107414,
    47227587164483933, 48393170323786442, 43758728967875397, 43758721888375110, 43125894395845251, 48393170323786442,
    48393169662883899, 43125839167247248, 48393368495294866, 49227586506937531, 48393169662883899, 47358688724724612,
    47358681612150409, 42126053975329776, 44959775078046910, 43125839167247248, 43758752142697981, 43758745063247826,
    37698016465436760, 37698009085671665, 1584962500724866, 3906890600547867, 3906890600547867, 1584962500724866
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 1890597987 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1887982451 / 1000000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 243521239847874118828425216, coefficient := (-243521239847874118828425216) }, { argument := 8378374696453403096054235136, coefficient := (-8378374696453403096054235136) }, { argument := 101591096777002425416325005312, coefficient := (-101591096777002425416325005312) }, { argument := 8378509284082812465665015808, coefficient := (-8378509284082812465665015808) }, { argument := 251034560731929211446493184, coefficient := (-251034560731929211446493184) }, { argument := 2702043007029234642903367680, coefficient := (-2702043007029234642903367680) }, { argument := 104062798057888591111876771840, coefficient := (-104062798057888591111876771840) }, { argument := 104062750392938552927526584320, coefficient := (-104062750392938552927526584320) }, { argument := 2701939579027087264172736512, coefficient := (-2701939579027087264172736512) }, { argument := 2702043007029234642903367680, coefficient := (-2702043007029234642903367680) }, { argument := 9631575567364062375523123200, coefficient := (-9631575567364062375523123200) }, { argument := 2701640728426394198747381760, coefficient := (-2701640728426394198747381760) }, { argument := 243521239847874118828425216, coefficient := (-243521239847874118828425216) }, { argument := 243520027362886740286111744, coefficient := (-243520027362886740286111744) }, { argument := 243520027362886740286111744, coefficient := (-243520027362886740286111744) }, { argument := 8378333582733242760513454080, coefficient := (-8378333582733242760513454080) }, { argument := 101590595927957759152095232000, coefficient := (-101590595927957759152095232000) }, { argument := 8378468169993356960679854080, coefficient := (-8378468169993356960679854080) }, { argument := 251033276627322858738024448, coefficient := (-251033276627322858738024448) }, { argument := 9631575567364062375523123200, coefficient := (-9631575567364062375523123200) }, { argument := 371065124682096045579646795776, coefficient := (-371065124682096045579646795776) }, { argument := 371064955559394831204689641472, coefficient := (-371064955559394831204689641472) }, { argument := 9631206287662230915055091712, coefficient := (-9631206287662230915055091712) }, { argument := 104062798057888591111876771840, coefficient := (-104062798057888591111876771840) }, { argument := 371065124682096045579646795776, coefficient := (-371065124682096045579646795776) }, { argument := 104048457104795179441306206208, coefficient := (-104048457104795179441306206208) }, { argument := 8378374696453403096054235136, coefficient := (-8378374696453403096054235136) }, { argument := 8378333582733242760513454080, coefficient := (-8378333582733242760513454080) }, { argument := 2701640728426394198747381760, coefficient := (-2701640728426394198747381760) }, { argument := 104048457104795179441306206208, coefficient := (-104048457104795179441306206208) }, { argument := 104048409439923391300481581056, coefficient := (-104048409439923391300481581056) }, { argument := 2701537307419462941229973504, coefficient := (-2701537307419462941229973504) }, { argument := 104062750392938552927526584320, coefficient := (-104062750392938552927526584320) }, { argument := 371064955559394831204689641472, coefficient := (-371064955559394831204689641472) }, { argument := 104048409439923391300481581056, coefficient := (-104048409439923391300481581056) }, { argument := 101591096777002425416325005312, coefficient := (-101591096777002425416325005312) }, { argument := 101590595927957759152095232000, coefficient := (-101590595927957759152095232000) }, { argument := 2701939579027087264172736512, coefficient := (-2701939579027087264172736512) }, { argument := 9631206287662230915055091712, coefficient := (-9631206287662230915055091712) }, { argument := 2701537307419462941229973504, coefficient := (-2701537307419462941229973504) }, { argument := 8378509284082812465665015808, coefficient := (-8378509284082812465665015808) }, { argument := 8378468169993356960679854080, coefficient := (-8378468169993356960679854080) }, { argument := 251034560731929211446493184, coefficient := (-251034560731929211446493184) }, { argument := 251033276627322858738024448, coefficient := (-251033276627322858738024448) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 237685073116236888616638349312, coefficient := 237685073116236888616638349312 }, { argument := 237683901969349136944625352704, coefficient := 237683901969349136944625352704 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 427059062073766931892958920704, coefficient := 427059062073766931892958920704 }, { argument := 1522785724193034340149829304320, coefficient := 1522785724193034340149829304320 }, { argument := 427000089161128855763530285056, coefficient := 427000089161128855763530285056 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 30070518605639382434347745280, coefficient := 30070518605639382434347745280 }, { argument := 1158352759689559632265659547648, coefficient := 1158352759689559632265659547648 }, { argument := 1158352230784513550865395613696, coefficient := 1158352230784513550865395613696 }, { argument := 30069366348217562240915603456, coefficient := 30069366348217562240915603456 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 974082534421521718229073920, coefficient := 974082534421521718229073920 }, { argument := 33513416558373291713135378432, coefficient := 33513416558373291713135378432 }, { argument := 406363385409920369136840474624, coefficient := 406363385409920369136840474624 }, { argument := 33513954908152338852689739776, coefficient := 33513954908152338852689739776 }, { argument := 1004135674718504140369035264, coefficient := 1004135674718504140369035264 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard0


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8
