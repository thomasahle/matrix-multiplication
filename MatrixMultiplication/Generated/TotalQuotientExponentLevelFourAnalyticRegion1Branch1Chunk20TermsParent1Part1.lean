import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 20, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1483853860000305248928036359766016)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6019803189, 3900610809, 52129269459, 40813708221, 1807600131, 104258501793,
    1807600131, 3520063413, 66500657451, 3520063413, 40813708221, 66500657451,
    1504953891, 3520063413, 3520063413, 3900610809, 981483, 464019957,
    17613827583, 1856081101, 981483, 4555450075, 88843540225, 177687015275,
    569433975, 1818805045, 11651465, 9654071, 26712269579, 64915305,
    1818804433, 259994119, 259994119, 186090541, 9654071, 1747570153,
    858820697, 2763296445, 7126396095, 5962902855, 166815843285, 6725129117,
    5962902855, 5381156235, 2763296445, 2763296445, 5381156235, 166815843285,
    5381156235, 218446263, 7126396095, 13670796903, 210520560393, 358604703555,
    72948687783, 113482501125, 13617900135, 358604703555, 712670107065, 113482501125,
    10998724009035, 703591506975, 210520564681, 358604703555
  ]
def negativeCoefficients : Array ℕ := #[
    27761442200395902469439225856, 17988392331192042439978254336, 480807646229808286946266447872, 188220007562960639189040758784, 16672168502080429578516430848, 480807475020964852829490511872,
    16672168502080429578516430848, 16233427225709891958029156352, 613360304366011593441209745408, 16233427225709891958029156352, 188220007562960639189040758784, 613360304366011593441209745408,
    27761499270010380508364537856, 16233427225709891958029156352, 16233427225709891958029156352, 17988392331192042439978254336, 144841325709573374789812224, 17119314783745421942691201024,
    162458884791023542692231512064, 17119326525098024858820804608, 144841325709573374789812224, 21008305418521495609330892800, 819437024566447456981404876800, 819436723999811205976398233600,
    21008405607400245944333107200, 8387757796271696085967175680, 214931592938784260819517440, 11130386062901327792439296, 30797150034484386832112943104, 299369004450449506141470720,
    8387754973919852808405778432, 299752810866411620892934144, 299752810866411620892934144, 214547786522822146068054016, 11130386062901327792439296, 8059244840811111098783629312,
    7921222801381928247205298176, 6371727790088302742879600640, 8216175308271758800028958720, 109996142902577015771816263680, 192325573032402190686392156160, 7753545980246956235861000192,
    109996142902577015771816263680, 6204050742980715828593295360, 6371727790088302742879600640, 6371727790088302742879600640, 6204050742980715828593295360, 192325573032402190686392156160,
    6204050742980715828593295360, 8059244614838496195841622016, 8216175308271758800028958720, 31522711469162767744191430656, 485427362477948313064634843136, 826886148763445853303456399360,
    168208221755742952432563388416, 523345663774332818546491392000, 31400739826459969112789483520, 826886148763445853303456399360, 821652692125702525117991485440, 523345663774332818546491392000,
    12680665433252084193381486428160, 811185778850215868747061657600, 485427372365403136572954509312, 826886148763445853303456399360
  ]
def negativeScales : Array ℕ := #[
    32, 31, 35, 35, 30, 36,
    30, 31, 35, 31, 35, 35,
    30, 31, 31, 31, 19, 28,
    34, 30, 19, 32, 36, 37,
    29, 30, 23, 23, 34, 25,
    30, 27, 27, 27, 23, 30,
    29, 31, 32, 32, 37, 32,
    32, 32, 31, 31, 32, 37,
    32, 27, 32, 33, 37, 38,
    36, 36, 33, 38, 39, 36,
    43, 39, 37, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32487069174377532, 31861052913972795, 35601374590987548, 35248334744718458, 30751428420894502, 36601374077264035,
    30751428420894502, 31712954272945749, 35952649563494608, 31712954272945749, 35248334744718458, 35952649563494608,
    30487072140144388, 31712954272945749, 31712954272945749, 31861052913972795, 19904603758558688, 28789611615072329,
    34035989397792020, 30789612604550340, 19904603758558688, 32084946452227257, 36370547831214722, 37370547302039127,
    29084953332442057, 30760343765214723, 23474008028134599, 23202706006317094, 34636783507088138, 25952055335730863,
    30760343279769886, 27953903760464169, 27953903760464169, 27471429484032813, 23202706006317094, 30702703225174114,
    29677781718735260, 31363743196009975, 32730525526827645, 32473367687184580, 37279465358582213, 32646914820510519,
    32473367687184580, 32325269048195338, 31363743196009975, 31363743196009975, 32325269048195338, 37279465358582213,
    32325269048195338, 27702703184722486, 32730525526827645, 33670378292401472, 37615170184084928, 38383603454864574,
    36086162975735291, 36723678896587312, 33664785207439524, 38383603454864574, 39374443455579097, 36723678896587312,
    43322401396138815, 39355947111961707, 37615170213470544, 38383603454864574
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 11846037963 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 27761442200395902469439225856, coefficient := (-27761442200395902469439225856) }, { argument := 17988392331192042439978254336, coefficient := (-17988392331192042439978254336) }, { argument := 480807646229808286946266447872, coefficient := (-480807646229808286946266447872) }, { argument := 188220007562960639189040758784, coefficient := (-188220007562960639189040758784) }, { argument := 16672168502080429578516430848, coefficient := (-16672168502080429578516430848) }, { argument := 480807475020964852829490511872, coefficient := (-480807475020964852829490511872) }, { argument := 16672168502080429578516430848, coefficient := (-16672168502080429578516430848) }, { argument := 16233427225709891958029156352, coefficient := (-16233427225709891958029156352) }, { argument := 613360304366011593441209745408, coefficient := (-613360304366011593441209745408) }, { argument := 16233427225709891958029156352, coefficient := (-16233427225709891958029156352) }, { argument := 188220007562960639189040758784, coefficient := (-188220007562960639189040758784) }, { argument := 613360304366011593441209745408, coefficient := (-613360304366011593441209745408) }, { argument := 27761499270010380508364537856, coefficient := (-27761499270010380508364537856) }, { argument := 16233427225709891958029156352, coefficient := (-16233427225709891958029156352) }, { argument := 16233427225709891958029156352, coefficient := (-16233427225709891958029156352) }, { argument := 17988392331192042439978254336, coefficient := (-17988392331192042439978254336) }, { argument := 144841325709573374789812224, coefficient := (-144841325709573374789812224) }, { argument := 17119314783745421942691201024, coefficient := (-17119314783745421942691201024) }, { argument := 162458884791023542692231512064, coefficient := (-162458884791023542692231512064) }, { argument := 17119326525098024858820804608, coefficient := (-17119326525098024858820804608) }, { argument := 144841325709573374789812224, coefficient := (-144841325709573374789812224) }, { argument := 21008305418521495609330892800, coefficient := (-21008305418521495609330892800) }, { argument := 819437024566447456981404876800, coefficient := (-819437024566447456981404876800) }, { argument := 819436723999811205976398233600, coefficient := (-819436723999811205976398233600) }, { argument := 21008405607400245944333107200, coefficient := (-21008405607400245944333107200) }, { argument := 8387757796271696085967175680, coefficient := (-8387757796271696085967175680) }, { argument := 214931592938784260819517440, coefficient := (-214931592938784260819517440) }, { argument := 11130386062901327792439296, coefficient := (-11130386062901327792439296) }, { argument := 30797150034484386832112943104, coefficient := (-30797150034484386832112943104) }, { argument := 299369004450449506141470720, coefficient := (-299369004450449506141470720) }, { argument := 8387754973919852808405778432, coefficient := (-8387754973919852808405778432) }, { argument := 299752810866411620892934144, coefficient := (-299752810866411620892934144) }, { argument := 299752810866411620892934144, coefficient := (-299752810866411620892934144) }, { argument := 214547786522822146068054016, coefficient := (-214547786522822146068054016) }, { argument := 11130386062901327792439296, coefficient := (-11130386062901327792439296) }, { argument := 8059244840811111098783629312, coefficient := (-8059244840811111098783629312) }, { argument := 7921222801381928247205298176, coefficient := (-7921222801381928247205298176) }, { argument := 6371727790088302742879600640, coefficient := (-6371727790088302742879600640) }, { argument := 8216175308271758800028958720, coefficient := (-8216175308271758800028958720) }, { argument := 109996142902577015771816263680, coefficient := (-109996142902577015771816263680) }, { argument := 192325573032402190686392156160, coefficient := (-192325573032402190686392156160) }, { argument := 7753545980246956235861000192, coefficient := (-7753545980246956235861000192) }, { argument := 109996142902577015771816263680, coefficient := (-109996142902577015771816263680) }, { argument := 6204050742980715828593295360, coefficient := (-6204050742980715828593295360) }, { argument := 6371727790088302742879600640, coefficient := (-6371727790088302742879600640) }, { argument := 6371727790088302742879600640, coefficient := (-6371727790088302742879600640) }, { argument := 6204050742980715828593295360, coefficient := (-6204050742980715828593295360) }, { argument := 192325573032402190686392156160, coefficient := (-192325573032402190686392156160) }, { argument := 6204050742980715828593295360, coefficient := (-6204050742980715828593295360) }, { argument := 8059244614838496195841622016, coefficient := (-8059244614838496195841622016) }, { argument := 8216175308271758800028958720, coefficient := (-8216175308271758800028958720) }, { argument := 31522711469162767744191430656, coefficient := (-31522711469162767744191430656) }, { argument := 485427362477948313064634843136, coefficient := (-485427362477948313064634843136) }, { argument := 826886148763445853303456399360, coefficient := (-826886148763445853303456399360) }, { argument := 168208221755742952432563388416, coefficient := (-168208221755742952432563388416) }, { argument := 523345663774332818546491392000, coefficient := (-523345663774332818546491392000) }, { argument := 31400739826459969112789483520, coefficient := (-31400739826459969112789483520) }, { argument := 826886148763445853303456399360, coefficient := (-826886148763445853303456399360) }, { argument := 821652692125702525117991485440, coefficient := (-821652692125702525117991485440) }, { argument := 523345663774332818546491392000, coefficient := (-523345663774332818546491392000) }, { argument := 12680665433252084193381486428160, coefficient := (-12680665433252084193381486428160) }, { argument := 811185778850215868747061657600, coefficient := (-811185778850215868747061657600) }, { argument := 485427372365403136572954509312, coefficient := (-485427372365403136572954509312) }, { argument := 826886148763445853303456399360, coefficient := (-826886148763445853303456399360) }] }

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

end TermShard2


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1743906770901431131085887567298560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    13617900135, 703591506975, 13617900135, 358604703555, 358604703555, 13670796903,
    16337431077, 148064076171, 17819081049, 1549255821399, 68615059689, 35638159623,
    68615059689, 133618800447, 2524311932769, 133618800447, 1549255821399, 2524311932769,
    32674862979, 133618800447, 133618800447, 148064076171, 981483, 464019957,
    17613827583, 1856081101, 981483, 1441598125, 28115044375, 56230068125,
    180200625, 1771067563, 2043557495, 1693233353, 50323934897, 11385534615,
    55345847, 45600525817, 45600525817, 32638532563, 1693233353, 172991775,
    3373805325, 6747608175, 21624075, 89877657, 10504953225, 2876084055,
    259994119, 45600525817, 11400132821, 64997163, 1911309, 903617811,
    34300611609, 3614473723, 1911309, 259994119, 45600525817, 11400132821,
    64997163, 36108243, 17071049997, 648003446343
  ]
def negativeCoefficients : Array ℕ := #[
    31400739826459969112789483520, 811185778850215868747061657600, 31400739826459969112789483520, 826886148763445853303456399360, 826886148763445853303456399360, 31522711469162767744191430656,
    150686204949644003621486985216, 170706257477292118062605008896, 164352013869795465165476462592, 1786170352628251674362379239424, 158215555710660987472658300928, 164352002455872569557691400192,
    158215555710660987472658300928, 154051988455117277276009398272, 5820667023250106854915165913088, 154051988455117277276009398272, 1786170352628251674362379239424, 5820667023250106854915165913088,
    150686208754284968824082006016, 154051988455117277276009398272, 154051988455117277276009398272, 170706257477292118062605008896, 144841325709573374789812224, 17119314783745421942691201024,
    162458884791023542692231512064, 17119326525098024858820804608, 144841325709573374789812224, 13296395834507275702108160000, 518631028206612314545192960000, 518630837974564054415441920000,
    13296459245190029078691840000, 8167607517977366987592957952, 37696982110175986657966161920, 1952165144991256451930390528, 58019546739186252800665321472, 52506510796316552845024296960,
    8167605401213484529421910016, 52573826835799009964056379392, 52573826835799009964056379392, 37629666070693529538934079488, 1952165144991256451930390528, 797783750070436542126489600,
    31117861692396738872711577600, 31117850278473843264926515200, 797787554711401744721510400, 6631800546494599191066574848, 24222772955983098995225395200, 6631798312132723262997135360,
    299752810866411620892934144, 52573826835799009964056379392, 52573833138820875649688797184, 299746507844545935260516352, 141029711875110917558501376, 16668806499962647681041432576,
    158183650980733449463488577536, 16668817932332287362536046592, 141029711875110917558501376, 299752810866411620892934144, 52573826835799009964056379392, 52573833138820875649688797184,
    299746507844545935260516352, 5328636140578515209372565504, 629810580728318417786376290304, 5976776866785550333782622470144
  ]
def negativeScales : Array ℕ := #[
    33, 39, 33, 38, 38, 33,
    33, 37, 34, 40, 35, 35,
    35, 36, 41, 36, 40, 41,
    34, 36, 36, 37, 19, 28,
    34, 30, 19, 30, 34, 35,
    27, 30, 30, 30, 35, 33,
    25, 35, 35, 34, 30, 27,
    31, 32, 24, 26, 33, 31,
    27, 35, 33, 25, 20, 29,
    34, 31, 20, 27, 35, 33,
    25, 25, 33, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33664785207439524, 39355947111961707, 33664785207439524, 38383603454864574, 38383603454864574, 33670378292401472,
    33927462105673171, 37107430695078630, 34052703886169172, 40494712527960319, 35997806226765703, 35052703785976846,
    35997806226765703, 36959332068282227, 41199027335835983, 36959332068282227, 40494712527960319, 41199027335835983,
    34927462142099447, 36959332068282227, 36959332068282227, 37107430695078630, 19904603758558688, 28789611615072329,
    34035989397792020, 30789612604550340, 19904603758558688, 30425021893824897, 34710623272905095, 35710622743729499,
    27425028774039697, 30721972103432933, 30928435695003678, 30657133666002926, 35550525681792534, 33406482984599453,
    25721971729535785, 35408331408991822, 35408331408991822, 34925857150586521, 30657133666002926, 27366128204771312,
    31651729583781036, 32651729054605441, 24366135084986112, 26421459179933871, 33290350687066327, 31421458693866276,
    27953903760464169, 35408331408991822, 33408331581955032, 25953873424015716, 20866129608350967, 29751137466966286,
    34997515272732868, 31751138456444292, 20866129608350967, 27953903760464169, 35408331408991822, 33408331581955032,
    25953873424015716, 25105824885748244, 33990832766923542, 39237210529723871
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 6734659199 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 31400739826459969112789483520, coefficient := (-31400739826459969112789483520) }, { argument := 811185778850215868747061657600, coefficient := (-811185778850215868747061657600) }, { argument := 31400739826459969112789483520, coefficient := (-31400739826459969112789483520) }, { argument := 826886148763445853303456399360, coefficient := (-826886148763445853303456399360) }, { argument := 826886148763445853303456399360, coefficient := (-826886148763445853303456399360) }, { argument := 31522711469162767744191430656, coefficient := (-31522711469162767744191430656) }, { argument := 150686204949644003621486985216, coefficient := (-150686204949644003621486985216) }, { argument := 170706257477292118062605008896, coefficient := (-170706257477292118062605008896) }, { argument := 164352013869795465165476462592, coefficient := (-164352013869795465165476462592) }, { argument := 1786170352628251674362379239424, coefficient := (-1786170352628251674362379239424) }, { argument := 158215555710660987472658300928, coefficient := (-158215555710660987472658300928) }, { argument := 164352002455872569557691400192, coefficient := (-164352002455872569557691400192) }, { argument := 158215555710660987472658300928, coefficient := (-158215555710660987472658300928) }, { argument := 154051988455117277276009398272, coefficient := (-154051988455117277276009398272) }, { argument := 5820667023250106854915165913088, coefficient := (-5820667023250106854915165913088) }, { argument := 154051988455117277276009398272, coefficient := (-154051988455117277276009398272) }, { argument := 1786170352628251674362379239424, coefficient := (-1786170352628251674362379239424) }, { argument := 5820667023250106854915165913088, coefficient := (-5820667023250106854915165913088) }, { argument := 150686208754284968824082006016, coefficient := (-150686208754284968824082006016) }, { argument := 154051988455117277276009398272, coefficient := (-154051988455117277276009398272) }, { argument := 154051988455117277276009398272, coefficient := (-154051988455117277276009398272) }, { argument := 170706257477292118062605008896, coefficient := (-170706257477292118062605008896) }, { argument := 144841325709573374789812224, coefficient := (-144841325709573374789812224) }, { argument := 17119314783745421942691201024, coefficient := (-17119314783745421942691201024) }, { argument := 162458884791023542692231512064, coefficient := (-162458884791023542692231512064) }, { argument := 17119326525098024858820804608, coefficient := (-17119326525098024858820804608) }, { argument := 144841325709573374789812224, coefficient := (-144841325709573374789812224) }, { argument := 13296395834507275702108160000, coefficient := (-13296395834507275702108160000) }, { argument := 518631028206612314545192960000, coefficient := (-518631028206612314545192960000) }, { argument := 518630837974564054415441920000, coefficient := (-518630837974564054415441920000) }, { argument := 13296459245190029078691840000, coefficient := (-13296459245190029078691840000) }, { argument := 8167607517977366987592957952, coefficient := (-8167607517977366987592957952) }, { argument := 37696982110175986657966161920, coefficient := (-37696982110175986657966161920) }, { argument := 1952165144991256451930390528, coefficient := (-1952165144991256451930390528) }, { argument := 58019546739186252800665321472, coefficient := (-58019546739186252800665321472) }, { argument := 52506510796316552845024296960, coefficient := (-52506510796316552845024296960) }, { argument := 8167605401213484529421910016, coefficient := (-8167605401213484529421910016) }, { argument := 52573826835799009964056379392, coefficient := (-52573826835799009964056379392) }, { argument := 52573826835799009964056379392, coefficient := (-52573826835799009964056379392) }, { argument := 37629666070693529538934079488, coefficient := (-37629666070693529538934079488) }, { argument := 1952165144991256451930390528, coefficient := (-1952165144991256451930390528) }, { argument := 797783750070436542126489600, coefficient := (-797783750070436542126489600) }, { argument := 31117861692396738872711577600, coefficient := (-31117861692396738872711577600) }, { argument := 31117850278473843264926515200, coefficient := (-31117850278473843264926515200) }, { argument := 797787554711401744721510400, coefficient := (-797787554711401744721510400) }, { argument := 6631800546494599191066574848, coefficient := (-6631800546494599191066574848) }, { argument := 24222772955983098995225395200, coefficient := (-24222772955983098995225395200) }, { argument := 6631798312132723262997135360, coefficient := (-6631798312132723262997135360) }, { argument := 299752810866411620892934144, coefficient := (-299752810866411620892934144) }, { argument := 52573826835799009964056379392, coefficient := (-52573826835799009964056379392) }, { argument := 52573833138820875649688797184, coefficient := (-52573833138820875649688797184) }, { argument := 299746507844545935260516352, coefficient := (-299746507844545935260516352) }, { argument := 141029711875110917558501376, coefficient := (-141029711875110917558501376) }, { argument := 16668806499962647681041432576, coefficient := (-16668806499962647681041432576) }, { argument := 158183650980733449463488577536, coefficient := (-158183650980733449463488577536) }, { argument := 16668817932332287362536046592, coefficient := (-16668817932332287362536046592) }, { argument := 141029711875110917558501376, coefficient := (-141029711875110917558501376) }, { argument := 299752810866411620892934144, coefficient := (-299752810866411620892934144) }, { argument := 52573826835799009964056379392, coefficient := (-52573826835799009964056379392) }, { argument := 52573833138820875649688797184, coefficient := (-52573833138820875649688797184) }, { argument := 299746507844545935260516352, coefficient := (-299746507844545935260516352) }, { argument := 5328636140578515209372565504, coefficient := (-5328636140578515209372565504) }, { argument := 629810580728318417786376290304, coefficient := (-629810580728318417786376290304) }, { argument := 5976776866785550333782622470144, coefficient := (-5976776866785550333782622470144) }] }

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

end TermShard3


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20
