import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 2, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 242069715018954582964418797109248
def positiveArguments : Array ℕ := #[
    9, 3, 87, 77, 5, 3,
    5, 153
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 232113757366008801543585792, 3365649481807127622381993984, 5957586439060892572952035328, 193428131138340667952988160, 3713820117856140824697372672,
    193428131138340667952988160, 5918900812833224439361437696
  ]
def positiveScales : Array ℕ := #[
    3, 1, 6, 6, 2, 1,
    2, 7
  ]
def negativeArguments : Array ℕ := #[
    4957815, 29104779, 401985, 3198807, 144580257, 401985,
    11993655, 2378759625, 2378759625, 11993655, 16876111, 456461803,
    77, 8931919365, 3, 5, 153, 5,
    3, 2451, 157, 456461803, 153, 5,
    157, 5, 153, 5, 16876111, 3913719,
    776226825, 776226825, 3913719, 33897787, 918887431, 77,
    17986638505, 3, 5, 153, 5, 3,
    2451, 157, 918887431, 153, 5, 157,
    5, 153, 5, 33897787, 614103, 6137931,
    12275859, 614103
  ]
def negativeCoefficients : Array ℕ := #[
    45727772234899160322539520, 67111051191859526246596608, 59322515331761072850862080, 59007574070190629676122112, 2667034998990153915996045312, 59322515331761072850862080,
    221243884293366932286996480, 43880370015248305360994304000, 43880370015248305360994304000, 221243884293366932286996480, 77827325144128643707961344, 8420234059365026828960923648,
    744698304882611571619004416, 82382415306582665732208721920, 464227514732017603087171584, 24178516392292583494123520, 739862601604153054920179712, 773712524553362671811952640,
    464227514732017603087171584, 11852308735501824428819349504, 759205414717987121715478528, 8420234059365026828960923648, 739862601604153054920179712, 24178516392292583494123520,
    759205414717987121715478528, 24178516392292583494123520, 739862601604153054920179712, 773712524553362671811952640, 77827325144128643707961344, 9024421596176809080127488,
    1789857197990391402882662400, 1789857197990391402882662400, 9024421596176809080127488, 78162975181764835068084224, 8475240636102722262294069248, 744698304882611571619004416,
    82948729312016194820657643520, 464227514732017603087171584, 24178516392292583494123520, 739862601604153054920179712, 773712524553362671811952640, 464227514732017603087171584,
    11852308735501824428819349504, 759205414717987121715478528, 8475240636102722262294069248, 739862601604153054920179712, 24178516392292583494123520, 759205414717987121715478528,
    24178516392292583494123520, 739862601604153054920179712, 773712524553362671811952640, 78162975181764835068084224, 2900019424229697734666354688, 115942238514266257264585211904,
    115942210180067360046713929728, 2900019424229697734666354688
  ]
def negativeScales : Array ℕ := #[
    22, 24, 18, 21, 27, 18,
    23, 31, 31, 23, 24, 28,
    6, 33, 1, 2, 7, 2,
    1, 11, 7, 28, 7, 2,
    7, 2, 7, 2, 24, 21,
    29, 29, 21, 25, 29, 6,
    34, 1, 2, 7, 2, 1,
    11, 7, 29, 7, 2, 7,
    2, 7, 2, 25, 19, 22,
    23, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 1584962500720924, 6442943495848725, 6266786540694901, 2321928094887362, 1584962500720924,
    2321928094887362, 7257387842692651
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    22241273007839948, 24794752727668323, 18616782142941091, 21609102519414729, 27107295319182916, 18616782142941091,
    23515768043299938, 31147562347968134, 31147562347968134, 23515768043299938, 24008479146015291, 28765918899082144,
    6266786540694902, 33056323080937095, 1584962500724866, 2321928094887363, 7257387842692652, 2321928094887363,
    1584962500724866, 11259154768866840, 7294620748891628, 28765918899082144, 7257387842692652, 2321928094887363,
    7294620748891628, 2321928094887363, 7257387842692652, 2321928094887363, 24008479146015291, 21900108749731547,
    29531903050024823, 29531903050024823, 21900108749731547, 25014687755026265, 29775312893377694, 6266786540694902,
    34066206537613853, 1584962500724866, 2321928094887363, 7257387842692652, 2321928094887363, 1584962500724866,
    11259154768866840, 7294620748891628, 29775312893377694, 7257387842692652, 2321928094887363, 7294620748891628,
    2321928094887363, 7257387842692652, 2321928094887363, 25014687755026265, 19228121125352790, 22549320997059275,
    23549320644490498, 19228121125352790
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 56
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
noncomputable def positiveFloor : ℝ := 22028863 / 200000000000
noncomputable def negativeCeiling : ℝ := 91913019 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 67111051191859526246596608, coefficient := (-67111051191859526246596608) }, { argument := 59322515331761072850862080, coefficient := (-59322515331761072850862080) }, { argument := 59007574070190629676122112, coefficient := (-59007574070190629676122112) }, { argument := 2667034998990153915996045312, coefficient := (-2667034998990153915996045312) }, { argument := 59322515331761072850862080, coefficient := (-59322515331761072850862080) }, { argument := 221243884293366932286996480, coefficient := (-221243884293366932286996480) }, { argument := 43880370015248305360994304000, coefficient := (-43880370015248305360994304000) }, { argument := 43880370015248305360994304000, coefficient := (-43880370015248305360994304000) }, { argument := 221243884293366932286996480, coefficient := (-221243884293366932286996480) }, { argument := 77827325144128643707961344, coefficient := (-77827325144128643707961344) }, { argument := 8420234059365026828960923648, coefficient := (-8420234059365026828960923648) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 82382415306582665732208721920, coefficient := (-82382415306582665732208721920) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 8420234059365026828960923648, coefficient := (-8420234059365026828960923648) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 77827325144128643707961344, coefficient := (-77827325144128643707961344) }, { argument := 9024421596176809080127488, coefficient := (-9024421596176809080127488) }, { argument := 1789857197990391402882662400, coefficient := (-1789857197990391402882662400) }, { argument := 1789857197990391402882662400, coefficient := (-1789857197990391402882662400) }, { argument := 9024421596176809080127488, coefficient := (-9024421596176809080127488) }, { argument := 78162975181764835068084224, coefficient := (-78162975181764835068084224) }, { argument := 8475240636102722262294069248, coefficient := (-8475240636102722262294069248) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 82948729312016194820657643520, coefficient := (-82948729312016194820657643520) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 8475240636102722262294069248, coefficient := (-8475240636102722262294069248) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 78162975181764835068084224, coefficient := (-78162975181764835068084224) }, { argument := 2900019424229697734666354688, coefficient := (-2900019424229697734666354688) }, { argument := 115942238514266257264585211904, coefficient := (-115942238514266257264585211904) }, { argument := 115942210180067360046713929728, coefficient := (-115942210180067360046713929728) }, { argument := 2900019424229697734666354688, coefficient := (-2900019424229697734666354688) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 5957586439060892572952035328, coefficient := 5957586439060892572952035328 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }] }

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

end TermShard4


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-56455484178047387371882516840448)
def positiveArguments : Array ℕ := #[
    5, 3, 2451, 157, 87, 153,
    5, 157, 5, 153, 5, 3,
    141, 105, 111, 9, 1929, 3489,
    105, 1929, 57, 57, 111, 111,
    3489, 111, 141, 9, 93, 285,
    843, 1881, 93, 939, 1911, 93,
    285, 93, 1285, 5125, 2545, 5125,
    3, 1, 1, 1, 1, 614103,
    6137931, 12275859, 614103, 20795, 851975, 17542825,
    851975, 20795
  ]
def positiveCoefficients : Array ℕ := #[
    6189700196426901374495621120, 3713820117856140824697372672, 94818469884014595430554796032, 6073643317743896973723828224, 3365649481807127622381993984, 5918900812833224439361437696,
    193428131138340667952988160, 6073643317743896973723828224, 193428131138340667952988160, 5918900812833224439361437696, 6189700196426901374495621120, 232113757366008801543585792,
    5454673298101206836274266112, 4061990753905154027012751360, 4294104511271162828556337152, 5570730176784211237046059008, 74624572993171829696262832128, 134974149908334118097595138048,
    4061990753905154027012751360, 74624572993171829696262832128, 4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152, 4294104511271162828556337152,
    134974149908334118097595138048, 4294104511271162828556337152, 5454673298101206836274266112, 5570730176784211237046059008, 7195526478346272847851159552, 176406455598166689173125201920,
    130447931639696946467495215104, 145535325868487518567828291584, 7195526478346272847851159552, 145303212111121509766284705792, 147856463442147606583264149504, 7195526478346272847851159552,
    176406455598166689173125201920, 7195526478346272847851159552, 198844118810214206655671828480, 198263834416799184651812864000, 196909837498830799976141946880, 198263834416799184651812864000,
    475368975085586025561263702016, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 5800038848459395469332709376,
    231884477028532514529170423808, 231884420360134720093427859456, 5800038848459395469332709376, 392806444045097088875233280, 64373410947885855695018393600, 662749190358781470367652249600,
    64373410947885855695018393600, 392806444045097088875233280
  ]
def positiveScales : Array ℕ := #[
    2, 1, 11, 7, 6, 7,
    2, 7, 2, 7, 2, 1,
    7, 6, 6, 3, 10, 11,
    6, 10, 5, 5, 6, 6,
    11, 6, 7, 3, 6, 8,
    9, 10, 6, 9, 10, 6,
    8, 6, 10, 12, 11, 12,
    1, 0, 0, 0, 0, 19,
    22, 23, 19, 14, 19, 24,
    19, 14
  ]
def negativeArguments : Array ℕ := #[
    1, 3, 3, 5, 3, 1,
    3, 5
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 475368975085586025561263702016, 950737950171172051122527404032, 792281625142643375935439503360, 475368975085586025561263702016, 158456325028528675187087900672,
    475368975085586025561263702016, 792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    0, 1, 1, 2, 1, 0,
    1, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 1584962500720924, 11259154768866839, 7294620748891626, 6442943495848725, 7257387842692651,
    2321928094887362, 7294620748891626, 2321928094887362, 7257387842692651, 2321928094887362, 1584962500720924,
    7139551352398793, 6714245517659862, 6794415866314396, 3169925001442312, 10913637427705176, 11768597882173550,
    6714245517659862, 10913637427705176, 5832890014087662, 5832890014087662, 6794415866314396, 6794415866314396,
    11768597882173550, 6794415866314396, 7139551352398793, 3169925001442312, 6539158811107971, 8154818109052103,
    9719388820935039, 10877284133344468, 6539158811107971, 9874981347482478, 10900112062706946, 6539158811107971,
    8154818109052103, 6539158811107971, 10327552644081240, 12323336289280170, 11313449940963057, 12323336289280170,
    1584962500720924, 0, 0, 0, 0, 19228121125352788,
    22549320997057889, 23549320644489112, 19228121125352788, 14343949064533718, 19700451571661328, 24064377754372501,
    19700451571661328, 14343949064533718
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 1584962500724866, 1584962500724866, 2321928094887363, 1584962500724866, 0,
    1584962500724866, 2321928094887363
  ]

abbrev PositiveTerm := Fin 56
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 658839979 / 1000000000000
noncomputable def negativeCeiling : ℝ := 17926681 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 147856463442147606583264149504, coefficient := 147856463442147606583264149504 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 5800038848459395469332709376, coefficient := 5800038848459395469332709376 }, { argument := 231884477028532514529170423808, coefficient := 231884477028532514529170423808 }, { argument := 231884420360134720093427859456, coefficient := 231884420360134720093427859456 }, { argument := 5800038848459395469332709376, coefficient := 5800038848459395469332709376 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 392806444045097088875233280, coefficient := 392806444045097088875233280 }, { argument := 64373410947885855695018393600, coefficient := 64373410947885855695018393600 }, { argument := 662749190358781470367652249600, coefficient := 662749190358781470367652249600 }, { argument := 64373410947885855695018393600, coefficient := 64373410947885855695018393600 }, { argument := 392806444045097088875233280, coefficient := 392806444045097088875233280 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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

end TermShard5


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2
