import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 14, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14

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
def constantNumerator : ℤ := (-190448235705565010725741006946304)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    37925, 179643, 716475, 355791, 716475, 252705753,
    11421840303, 31756815, 9509, 37925, 18833, 37925,
    502212699, 22699100349, 63111645, 6990879, 1226134497, 306533661,
    1747683, 110253, 439725, 218361, 439725, 79970175,
    3614506425, 10049625, 179643, 716475, 355791, 716475,
    7750709361, 350317962711, 974009655, 5849511, 1025949273, 256487349,
    1462347, 495815085, 22409939835, 62307675, 163643637, 28701556491,
    7175389983, 40910049, 16791609, 7938641511, 301344501909, 31754587823,
    16791609, 149559, 149505, 149379, 149505, 1598667893,
    31754587823, 37071291667, 13403734141, 1310775263, 13403734141, 26765185209,
    1600204463, 31754587823, 1310775263, 1256151285
  ]
def negativeCoefficients : Array ℕ := #[
    179095748862831294729420800, 6786720656657213400991924224, 6766915051628058108965683200, 6720701973226695760904454144, 6766915051628058108965683200, 582699793943132468051705856,
    26336970615027769920460947456, 585809838901140594402263040, 179619931542429825348141056, 179095748862831294729420800, 177872655943768056619073536, 179095748862831294729420800,
    579011820563745553696948224, 26170280927590885300711194624, 582102181692905527349084160, 128958955763270556491710464, 22618189266105591994779697152, 22618191977776970830083784704,
    128956244091891721187622912, 2082620287343307974982500352, 2076542601679854741592473600, 2062361335131797197015744512, 2076542601679854741592473600, 368797337938691435475763200,
    16668968743688461974975283200, 370765720823506705317888000, 6786720656657213400991924224, 6766915051628058108965683200, 6720701973226695760904454144, 6766915051628058108965683200,
    8935959498254493481577742336, 403889112659571433653651111936, 8983653415553567469852426240, 1726470917973581327725756416, 302806778746229966297458802688, 302806815049422303357856382976,
    1726434614781244267328176128, 571635873804971724987432960, 25836901552717116061211688960, 574686867276435393242726400, 3018692291030027108081467392, 529450267106594163632904339456,
    529450330581840521267471450112, 3018628815783669473514356736, 309750513808797970301190144, 36610522061585972553993682944, 347426556545925150853702877184, 36610547171063421386513973248,
    309750513808797970301190144, 1412544817623002537030320128, 1412034802042852615347240960, 1410844765689169464753389568, 1412034802042852615347240960, 1843138592564217848495341568,
    36610547171063421386513973248, 42740289366436908412532948992, 30906906666383767189147615232, 1511220988419395556567154688, 30906906666383767189147615232, 30858157602241206042161577984,
    1844910137160551591353253888, 36610547171063421386513973248, 1511220988419395556567154688, 23171901272256387979212226560
  ]
def negativeScales : Array ℕ := #[
    15, 17, 19, 18, 19, 27,
    33, 24, 13, 15, 14, 15,
    28, 34, 25, 22, 30, 28,
    20, 16, 18, 17, 18, 26,
    31, 23, 17, 19, 18, 19,
    32, 38, 29, 22, 29, 27,
    20, 28, 34, 25, 27, 34,
    32, 25, 24, 32, 38, 34,
    24, 17, 17, 17, 17, 30,
    34, 35, 33, 30, 33, 34,
    30, 34, 30, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15210861560021759, 17454773194569371, 19450556839768293, 18440670491451165, 19450556839768293, 27912883273077072,
    33411076067360029, 24920562897395069, 13215077914822828, 15210861560021759, 14200975211704646, 15210861560021759,
    28903723272967495, 34401916068074550, 25911402897174510, 22737042434137255, 30191470093628594, 28191470266591804,
    20737012097694363, 16750458386920568, 18746242032099458, 17736355683741649, 18746242032099458, 26252958709182194,
    31751151509188247, 23260638332706879, 17454773194569371, 19450556839768293, 18440670491451165, 19450556839768293,
    32851681210647364, 38349874008634263, 29859360834452284, 22479884594471294, 29934312262109986, 27934312435073220,
    20479854258028517, 28885226928024954, 34383419724457157, 25892906552050300, 27285982265868899, 34740409925711307,
    32740410098674518, 25285951929426122, 24001237142556879, 32886245006696804, 38132622786532506, 34886245996174866,
    24001237142556879, 17190355204450640, 17189834208723607, 17188617819850863, 17189834208723607, 30574223118707419,
    34886245996174866, 35109583332417813, 33641915925411329, 30287773205641476, 33641915925411329, 34639638584699274,
    30575609108420636, 34886245996174866, 30287773205641476, 30226363080139160
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
noncomputable def negativeCeiling : ℝ := 1195209753 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 6786720656657213400991924224, coefficient := (-6786720656657213400991924224) }, { argument := 6766915051628058108965683200, coefficient := (-6766915051628058108965683200) }, { argument := 6720701973226695760904454144, coefficient := (-6720701973226695760904454144) }, { argument := 6766915051628058108965683200, coefficient := (-6766915051628058108965683200) }, { argument := 582699793943132468051705856, coefficient := (-582699793943132468051705856) }, { argument := 26336970615027769920460947456, coefficient := (-26336970615027769920460947456) }, { argument := 585809838901140594402263040, coefficient := (-585809838901140594402263040) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 579011820563745553696948224, coefficient := (-579011820563745553696948224) }, { argument := 26170280927590885300711194624, coefficient := (-26170280927590885300711194624) }, { argument := 582102181692905527349084160, coefficient := (-582102181692905527349084160) }, { argument := 128958955763270556491710464, coefficient := (-128958955763270556491710464) }, { argument := 22618189266105591994779697152, coefficient := (-22618189266105591994779697152) }, { argument := 22618191977776970830083784704, coefficient := (-22618191977776970830083784704) }, { argument := 128956244091891721187622912, coefficient := (-128956244091891721187622912) }, { argument := 2082620287343307974982500352, coefficient := (-2082620287343307974982500352) }, { argument := 2076542601679854741592473600, coefficient := (-2076542601679854741592473600) }, { argument := 2062361335131797197015744512, coefficient := (-2062361335131797197015744512) }, { argument := 2076542601679854741592473600, coefficient := (-2076542601679854741592473600) }, { argument := 368797337938691435475763200, coefficient := (-368797337938691435475763200) }, { argument := 16668968743688461974975283200, coefficient := (-16668968743688461974975283200) }, { argument := 370765720823506705317888000, coefficient := (-370765720823506705317888000) }, { argument := 6786720656657213400991924224, coefficient := (-6786720656657213400991924224) }, { argument := 6766915051628058108965683200, coefficient := (-6766915051628058108965683200) }, { argument := 6720701973226695760904454144, coefficient := (-6720701973226695760904454144) }, { argument := 6766915051628058108965683200, coefficient := (-6766915051628058108965683200) }, { argument := 8935959498254493481577742336, coefficient := (-8935959498254493481577742336) }, { argument := 403889112659571433653651111936, coefficient := (-403889112659571433653651111936) }, { argument := 8983653415553567469852426240, coefficient := (-8983653415553567469852426240) }, { argument := 1726470917973581327725756416, coefficient := (-1726470917973581327725756416) }, { argument := 302806778746229966297458802688, coefficient := (-302806778746229966297458802688) }, { argument := 302806815049422303357856382976, coefficient := (-302806815049422303357856382976) }, { argument := 1726434614781244267328176128, coefficient := (-1726434614781244267328176128) }, { argument := 571635873804971724987432960, coefficient := (-571635873804971724987432960) }, { argument := 25836901552717116061211688960, coefficient := (-25836901552717116061211688960) }, { argument := 574686867276435393242726400, coefficient := (-574686867276435393242726400) }, { argument := 3018692291030027108081467392, coefficient := (-3018692291030027108081467392) }, { argument := 529450267106594163632904339456, coefficient := (-529450267106594163632904339456) }, { argument := 529450330581840521267471450112, coefficient := (-529450330581840521267471450112) }, { argument := 3018628815783669473514356736, coefficient := (-3018628815783669473514356736) }, { argument := 309750513808797970301190144, coefficient := (-309750513808797970301190144) }, { argument := 36610522061585972553993682944, coefficient := (-36610522061585972553993682944) }, { argument := 347426556545925150853702877184, coefficient := (-347426556545925150853702877184) }, { argument := 36610547171063421386513973248, coefficient := (-36610547171063421386513973248) }, { argument := 309750513808797970301190144, coefficient := (-309750513808797970301190144) }, { argument := 1412544817623002537030320128, coefficient := (-1412544817623002537030320128) }, { argument := 1412034802042852615347240960, coefficient := (-1412034802042852615347240960) }, { argument := 1410844765689169464753389568, coefficient := (-1410844765689169464753389568) }, { argument := 1412034802042852615347240960, coefficient := (-1412034802042852615347240960) }, { argument := 1843138592564217848495341568, coefficient := (-1843138592564217848495341568) }, { argument := 36610547171063421386513973248, coefficient := (-36610547171063421386513973248) }, { argument := 42740289366436908412532948992, coefficient := (-42740289366436908412532948992) }, { argument := 30906906666383767189147615232, coefficient := (-30906906666383767189147615232) }, { argument := 1511220988419395556567154688, coefficient := (-1511220988419395556567154688) }, { argument := 30906906666383767189147615232, coefficient := (-30906906666383767189147615232) }, { argument := 30858157602241206042161577984, coefficient := (-30858157602241206042161577984) }, { argument := 1844910137160551591353253888, coefficient := (-1844910137160551591353253888) }, { argument := 36610547171063421386513973248, coefficient := (-36610547171063421386513973248) }, { argument := 1511220988419395556567154688, coefficient := (-1511220988419395556567154688) }, { argument := 23171901272256387979212226560, coefficient := (-23171901272256387979212226560) }] }

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
def constantNumerator : ℤ := (-263844051831806368073911042572288)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1814178705, 990499925, 2554447175, 2137394575, 59794916525, 3576226045,
    2137394575, 1928868275, 990499925, 990499925, 1928868275, 59794916525,
    1928868275, 314037795, 2554447175, 252705753, 11421840303, 31756815,
    5849511, 1025949273, 256487349, 1462347, 535518939, 18535637583,
    11421840303, 229183089513, 3614506425, 433740771, 11421840303, 22699100349,
    3614506425, 350317962711, 22409939835, 37071291667, 11421840303, 433740771,
    22409939835, 433740771, 11421840303, 11421840303, 535518939, 5278827,
    925856661, 231464193, 1319679, 7087803, 3350931237, 127198677903,
    13403734141, 7087803, 1196467, 10537, 20513097, 110253,
    4883, 41026179, 4883, 9509, 179643, 9509,
    110253, 179643, 149559, 9509
  ]
def negativeCoefficients : Array ℕ := #[
    33465690275108818896845537280, 18271498621503505347431628800, 23560616643517677948003942400, 315423765676481565997767065600, 551510761022750542986949427200, 32984863300924749127205519360,
    315423765676481565997767065600, 17790669710411307838288691200, 18271498621503505347431628800, 18271498621503505347431628800, 17790669710411307838288691200, 551510761022750542986949427200,
    17790669710411307838288691200, 23171899335348260239709306880, 23560616643517677948003942400, 582699793943132468051705856, 26336970615027769920460947456, 585809838901140594402263040,
    1726470917973581327725756416, 302806778746229966297458802688, 302806815049422303357856382976, 1726434614781244267328176128, 1234822601794684609445756928, 42740270342079160894950998016,
    26336970615027769920460947456, 264230112391773652373301362688, 16668968743688461974975283200, 1000138124621307718498516992, 26336970615027769920460947456, 26170280927590885300711194624,
    16668968743688461974975283200, 403889112659571433653651111936, 25836901552717116061211688960, 42740289366436908412532948992, 26336970615027769920460947456, 1000138124621307718498516992,
    25836901552717116061211688960, 1000138124621307718498516992, 26336970615027769920460947456, 26336970615027769920460947456, 1234822601794684609445756928, 97377170678387971228434432,
    17079040874406263342996914176, 17079042921994855524757143552, 97375123089795789468205056, 261493775971741562145079296, 30906885468768983487659114496, 293300182223856918297267142656,
    30906906666383767189147615232, 261493775971741562145079296, 1412538914664898949973803008, 199038302519989806466859008, 48435180866326935312065888256, 2082620287343307974982500352,
    184474524286819820627820544, 48435163157452624550896336896, 184474524286819820627820544, 179619931542429825348141056, 6786720656657213400991924224, 179619931542429825348141056,
    2082620287343307974982500352, 6786720656657213400991924224, 1412544817623002537030320128, 179619931542429825348141056
  ]
def negativeScales : Array ℕ := #[
    30, 29, 31, 30, 35, 31,
    30, 30, 29, 29, 30, 35,
    30, 28, 31, 27, 33, 24,
    22, 29, 27, 20, 28, 34,
    33, 37, 31, 28, 33, 34,
    31, 38, 34, 35, 33, 28,
    34, 28, 33, 33, 28, 22,
    29, 27, 20, 22, 31, 36,
    33, 22, 20, 13, 24, 16,
    12, 25, 12, 13, 17, 13,
    16, 17, 17, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30756669429252040, 29883581628217962, 31250363955645373, 30993206137385165, 35799303788182913, 31735790782979939,
    30993206137385165, 30845107478736336, 29883581628217962, 29883581628217962, 30845107478736336, 35799303788182913,
    30845107478736336, 28226362959546213, 31250363955645373, 27912883273077072, 33411076067360029, 24920562897395069,
    22479884594471294, 29934312262109986, 27934312435073220, 20479854258028517, 28996362379230506, 34109582690252000,
    33411076067360029, 37737709641361609, 31751151509188247, 28692257819964341, 33411076067360029, 34401916068074550,
    31751151509188247, 38349874008634263, 34383419724457157, 35109583332417813, 33411076067360029, 28692257819964341,
    34383419724457157, 28692257819964341, 33411076067360029, 33411076067360029, 28996362379230506, 22331785955482024,
    29786213615628785, 27786213788591997, 20331755619039247, 22756907075443343, 31641914935933328, 36888292722692984,
    33641915925411329, 22756907075443343, 20190349175483579, 13363176553811964, 24290041985831383, 16750458386920568,
    12253552062637464, 25290041458353022, 12253552062637464, 13215077914822828, 17454773194569371, 13215077914822828,
    16750458386920568, 17454773194569371, 17190355204450640, 13215077914822828
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
noncomputable def negativeCeiling : ℝ := 832711839 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33465690275108818896845537280, coefficient := (-33465690275108818896845537280) }, { argument := 18271498621503505347431628800, coefficient := (-18271498621503505347431628800) }, { argument := 23560616643517677948003942400, coefficient := (-23560616643517677948003942400) }, { argument := 315423765676481565997767065600, coefficient := (-315423765676481565997767065600) }, { argument := 551510761022750542986949427200, coefficient := (-551510761022750542986949427200) }, { argument := 32984863300924749127205519360, coefficient := (-32984863300924749127205519360) }, { argument := 315423765676481565997767065600, coefficient := (-315423765676481565997767065600) }, { argument := 17790669710411307838288691200, coefficient := (-17790669710411307838288691200) }, { argument := 18271498621503505347431628800, coefficient := (-18271498621503505347431628800) }, { argument := 18271498621503505347431628800, coefficient := (-18271498621503505347431628800) }, { argument := 17790669710411307838288691200, coefficient := (-17790669710411307838288691200) }, { argument := 551510761022750542986949427200, coefficient := (-551510761022750542986949427200) }, { argument := 17790669710411307838288691200, coefficient := (-17790669710411307838288691200) }, { argument := 23171899335348260239709306880, coefficient := (-23171899335348260239709306880) }, { argument := 23560616643517677948003942400, coefficient := (-23560616643517677948003942400) }, { argument := 582699793943132468051705856, coefficient := (-582699793943132468051705856) }, { argument := 26336970615027769920460947456, coefficient := (-26336970615027769920460947456) }, { argument := 585809838901140594402263040, coefficient := (-585809838901140594402263040) }, { argument := 1726470917973581327725756416, coefficient := (-1726470917973581327725756416) }, { argument := 302806778746229966297458802688, coefficient := (-302806778746229966297458802688) }, { argument := 302806815049422303357856382976, coefficient := (-302806815049422303357856382976) }, { argument := 1726434614781244267328176128, coefficient := (-1726434614781244267328176128) }, { argument := 1234822601794684609445756928, coefficient := (-1234822601794684609445756928) }, { argument := 42740270342079160894950998016, coefficient := (-42740270342079160894950998016) }, { argument := 26336970615027769920460947456, coefficient := (-26336970615027769920460947456) }, { argument := 264230112391773652373301362688, coefficient := (-264230112391773652373301362688) }, { argument := 16668968743688461974975283200, coefficient := (-16668968743688461974975283200) }, { argument := 1000138124621307718498516992, coefficient := (-1000138124621307718498516992) }, { argument := 26336970615027769920460947456, coefficient := (-26336970615027769920460947456) }, { argument := 26170280927590885300711194624, coefficient := (-26170280927590885300711194624) }, { argument := 16668968743688461974975283200, coefficient := (-16668968743688461974975283200) }, { argument := 403889112659571433653651111936, coefficient := (-403889112659571433653651111936) }, { argument := 25836901552717116061211688960, coefficient := (-25836901552717116061211688960) }, { argument := 42740289366436908412532948992, coefficient := (-42740289366436908412532948992) }, { argument := 26336970615027769920460947456, coefficient := (-26336970615027769920460947456) }, { argument := 1000138124621307718498516992, coefficient := (-1000138124621307718498516992) }, { argument := 25836901552717116061211688960, coefficient := (-25836901552717116061211688960) }, { argument := 1000138124621307718498516992, coefficient := (-1000138124621307718498516992) }, { argument := 26336970615027769920460947456, coefficient := (-26336970615027769920460947456) }, { argument := 26336970615027769920460947456, coefficient := (-26336970615027769920460947456) }, { argument := 1234822601794684609445756928, coefficient := (-1234822601794684609445756928) }, { argument := 97377170678387971228434432, coefficient := (-97377170678387971228434432) }, { argument := 17079040874406263342996914176, coefficient := (-17079040874406263342996914176) }, { argument := 17079042921994855524757143552, coefficient := (-17079042921994855524757143552) }, { argument := 97375123089795789468205056, coefficient := (-97375123089795789468205056) }, { argument := 261493775971741562145079296, coefficient := (-261493775971741562145079296) }, { argument := 30906885468768983487659114496, coefficient := (-30906885468768983487659114496) }, { argument := 293300182223856918297267142656, coefficient := (-293300182223856918297267142656) }, { argument := 30906906666383767189147615232, coefficient := (-30906906666383767189147615232) }, { argument := 261493775971741562145079296, coefficient := (-261493775971741562145079296) }, { argument := 1412538914664898949973803008, coefficient := (-1412538914664898949973803008) }, { argument := 199038302519989806466859008, coefficient := (-199038302519989806466859008) }, { argument := 48435180866326935312065888256, coefficient := (-48435180866326935312065888256) }, { argument := 2082620287343307974982500352, coefficient := (-2082620287343307974982500352) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 48435163157452624550896336896, coefficient := (-48435163157452624550896336896) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 6786720656657213400991924224, coefficient := (-6786720656657213400991924224) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 2082620287343307974982500352, coefficient := (-2082620287343307974982500352) }, { argument := 6786720656657213400991924224, coefficient := (-6786720656657213400991924224) }, { argument := 1412544817623002537030320128, coefficient := (-1412544817623002537030320128) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14
