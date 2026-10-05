import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-60715490384619760940056703926272)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3188320835, 612400273, 18095809, 18095809, 35239207, 35239207,
    1107653993, 35239207, 60670691, 2857233, 59497853, 7374296903,
    204144633, 73559795675, 7953687, 13256145, 405638037, 13256145,
    7953687, 6498162279, 416242953, 7374296903, 405638037, 13256145,
    416242953, 13256145, 405638037, 13256145, 59497853, 217256959,
    4689825, 1847373023, 52928025, 4689825, 3694745147, 4689825,
    4689825, 194426745, 1205955, 52928025, 194426745, 217256959,
    4689825, 1205955, 4689825, 2782371, 113994255, 2347229985,
    113994255, 2782371, 563951255, 5636666635, 11273330515, 563951255,
    378343263, 2756427911, 756687035, 184026199, 1839333323, 3678665747,
    184026199, 761889675, 5550763475, 1523780375
  ]
def negativeCoefficients : Array ℕ := #[
    7351767308515117394475089920, 1412098888337607691543248896, 83452189357432491879694336, 83452189357432491879694336, 81256079111184268409176064, 81256079111184268409176064,
    2554076216386683896212750336, 81256079111184268409176064, 139897088706514178730360832, 105413291819914726584877056, 137192708403274008343085056, 17003970961648743775423430656,
    941450949743090340810719232, 169617340616386469521103257600, 586878514125562809856032768, 30566589277373063013335040, 935337631887615728208052224, 978130856875938016426721280,
    586878514125562809856032768, 14983742063768275489136836608, 959790903309514178618720256, 17003970961648743775423430656, 935337631887615728208052224, 30566589277373063013335040,
    959790903309514178618720256, 30566589277373063013335040, 935337631887615728208052224, 978130856875938016426721280, 137192708403274008343085056, 250480220056588064584105984,
    43256000762742448953753600, 8519504340989037298206113792, 488174865750950495335219200, 43256000762742448953753600, 8519502268036172015095250944, 43256000762742448953753600,
    43256000762742448953753600, 1793270203049694098054184960, 44491886498820804638146560, 488174865750950495335219200, 1793270203049694098054184960, 250480220056588064584105984,
    43256000762742448953753600, 44491886498820804638146560, 43256000762742448953753600, 102651371510222637678723072, 16822582782865483382799728640, 173195003261728438935921623040,
    16822582782865483382799728640, 102651371510222637678723072, 5201532235516157069665239040, 207956293689325220549435064320, 207956242868545297479620362240, 5201532235516157069665239040,
    3489600672286592136332181504, 12711780057961712345409388544, 3489603019634775515872624640, 212167762238159038367924224, 8482427768906686627674324992, 8482425695953821344563462144,
    212167762238159038367924224, 3513595961781686581277491200, 12799189154627460858590003200, 3513598325270771025313792000
  ]
def negativeScales : Array ℕ := #[
    31, 29, 24, 24, 25, 25,
    30, 25, 25, 21, 25, 32,
    27, 36, 22, 23, 28, 23,
    22, 32, 28, 32, 28, 23,
    28, 23, 28, 23, 25, 27,
    22, 30, 25, 22, 31, 22,
    22, 27, 20, 25, 27, 27,
    22, 20, 22, 21, 26, 31,
    26, 21, 29, 32, 33, 29,
    28, 31, 29, 27, 30, 31,
    27, 29, 32, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31570149666433103, 29189899685071248, 24109152271186886, 24109152271186886, 25070678123372250, 25070678123372250,
    30044860139216519, 25070678123372250, 25854496408927902, 21446187258464497, 25826334274531371, 32779858357616843,
    27605016398448690, 36098198421295122, 22923192365049554, 23660157952662189, 28595617700444954, 23660157952662189,
    22923192365049554, 32597384626619394, 28632850606652610, 32779858357616843, 28595617700444954, 23660157952662189,
    28632850606652610, 23660157952662189, 28595617700444954, 23660157952662189, 25826334274531371, 27694827148188809,
    22161102659155964, 30782828060281280, 25657528485301237, 22161102659155964, 31782827709246866, 22161102659155964,
    22161102659155964, 27534651446278572, 20201744643653310, 25657528485301237, 27534651446278572, 27694827148188809,
    22161102659155964, 20201744643653310, 22161102659155964, 21407883370287827, 26764385877726947, 31128312060126600,
    26764385877726947, 21407883370287827, 29070995228090153, 32392195099795340, 33392194747226563, 29070995228090153,
    28495120514991752, 31360152725031546, 29495121485448478, 27455335930146138, 30776535802248583, 31776535449679803,
    27455335930146138, 29505006863308955, 32370039073348660, 30505007833765682
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
noncomputable def negativeCeiling : ℝ := 373887117 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7351767308515117394475089920, coefficient := (-7351767308515117394475089920) }, { argument := 1412098888337607691543248896, coefficient := (-1412098888337607691543248896) }, { argument := 83452189357432491879694336, coefficient := (-83452189357432491879694336) }, { argument := 83452189357432491879694336, coefficient := (-83452189357432491879694336) }, { argument := 81256079111184268409176064, coefficient := (-81256079111184268409176064) }, { argument := 81256079111184268409176064, coefficient := (-81256079111184268409176064) }, { argument := 2554076216386683896212750336, coefficient := (-2554076216386683896212750336) }, { argument := 81256079111184268409176064, coefficient := (-81256079111184268409176064) }, { argument := 139897088706514178730360832, coefficient := (-139897088706514178730360832) }, { argument := 105413291819914726584877056, coefficient := (-105413291819914726584877056) }, { argument := 137192708403274008343085056, coefficient := (-137192708403274008343085056) }, { argument := 17003970961648743775423430656, coefficient := (-17003970961648743775423430656) }, { argument := 941450949743090340810719232, coefficient := (-941450949743090340810719232) }, { argument := 169617340616386469521103257600, coefficient := (-169617340616386469521103257600) }, { argument := 586878514125562809856032768, coefficient := (-586878514125562809856032768) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 978130856875938016426721280, coefficient := (-978130856875938016426721280) }, { argument := 586878514125562809856032768, coefficient := (-586878514125562809856032768) }, { argument := 14983742063768275489136836608, coefficient := (-14983742063768275489136836608) }, { argument := 959790903309514178618720256, coefficient := (-959790903309514178618720256) }, { argument := 17003970961648743775423430656, coefficient := (-17003970961648743775423430656) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 959790903309514178618720256, coefficient := (-959790903309514178618720256) }, { argument := 30566589277373063013335040, coefficient := (-30566589277373063013335040) }, { argument := 935337631887615728208052224, coefficient := (-935337631887615728208052224) }, { argument := 978130856875938016426721280, coefficient := (-978130856875938016426721280) }, { argument := 137192708403274008343085056, coefficient := (-137192708403274008343085056) }, { argument := 250480220056588064584105984, coefficient := (-250480220056588064584105984) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 8519504340989037298206113792, coefficient := (-8519504340989037298206113792) }, { argument := 488174865750950495335219200, coefficient := (-488174865750950495335219200) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 8519502268036172015095250944, coefficient := (-8519502268036172015095250944) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 1793270203049694098054184960, coefficient := (-1793270203049694098054184960) }, { argument := 44491886498820804638146560, coefficient := (-44491886498820804638146560) }, { argument := 488174865750950495335219200, coefficient := (-488174865750950495335219200) }, { argument := 1793270203049694098054184960, coefficient := (-1793270203049694098054184960) }, { argument := 250480220056588064584105984, coefficient := (-250480220056588064584105984) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 44491886498820804638146560, coefficient := (-44491886498820804638146560) }, { argument := 43256000762742448953753600, coefficient := (-43256000762742448953753600) }, { argument := 102651371510222637678723072, coefficient := (-102651371510222637678723072) }, { argument := 16822582782865483382799728640, coefficient := (-16822582782865483382799728640) }, { argument := 173195003261728438935921623040, coefficient := (-173195003261728438935921623040) }, { argument := 16822582782865483382799728640, coefficient := (-16822582782865483382799728640) }, { argument := 102651371510222637678723072, coefficient := (-102651371510222637678723072) }, { argument := 5201532235516157069665239040, coefficient := (-5201532235516157069665239040) }, { argument := 207956293689325220549435064320, coefficient := (-207956293689325220549435064320) }, { argument := 207956242868545297479620362240, coefficient := (-207956242868545297479620362240) }, { argument := 5201532235516157069665239040, coefficient := (-5201532235516157069665239040) }, { argument := 3489600672286592136332181504, coefficient := (-3489600672286592136332181504) }, { argument := 12711780057961712345409388544, coefficient := (-12711780057961712345409388544) }, { argument := 3489603019634775515872624640, coefficient := (-3489603019634775515872624640) }, { argument := 212167762238159038367924224, coefficient := (-212167762238159038367924224) }, { argument := 8482427768906686627674324992, coefficient := (-8482427768906686627674324992) }, { argument := 8482425695953821344563462144, coefficient := (-8482425695953821344563462144) }, { argument := 212167762238159038367924224, coefficient := (-212167762238159038367924224) }, { argument := 3513595961781686581277491200, coefficient := (-3513595961781686581277491200) }, { argument := 12799189154627460858590003200, coefficient := (-12799189154627460858590003200) }, { argument := 3513598325270771025313792000, coefficient := (-3513598325270771025313792000) }] }

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

end TermShard6


end Parent3

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 6059725312624716353965671732740096
def positiveArguments : Array ℕ := #[
    3, 93, 105, 45, 1185, 105,
    45, 105, 105, 4353, 27, 1185,
    4353, 93, 105, 27, 105, 189,
    5481, 4851, 315, 189, 315, 9639,
    315, 189, 154413, 9891, 5481, 9639,
    315, 9891, 315, 9639, 315, 189,
    5311, 3955, 4181, 339, 72659, 131419,
    3955, 72659, 2147, 2147, 4181, 4181,
    131419, 4181, 5311, 339, 217, 665,
    1967, 4389, 217, 2191, 4459, 217,
    665
  ]
def positiveCoefficients : Array ℕ := #[
    60847228810955011271841753858048, 3597763239173136423925579776, 4061990753905154027012751360, 3481706360490132023153786880, 45842467079786738304858193920, 4061990753905154027012751360,
    3481706360490132023153786880, 4061990753905154027012751360, 4061990753905154027012751360, 168398530969039385519871492096, 4178047632588158427784544256, 45842467079786738304858193920,
    168398530969039385519871492096, 3597763239173136423925579776, 4061990753905154027012751360, 4178047632588158427784544256, 4061990753905154027012751360, 29246333428117108994491809792,
    424071834707698080420131241984, 750655891321672464191956451328, 24371944523430924162076508160, 467941334849873743911868956672, 24371944523430924162076508160, 745781502416986279359541149696,
    779902224749789573186448261120, 467941334849873743911868956672, 11947127205385839024249904300032, 765279058035731018689202356224, 424071834707698080420131241984, 745781502416986279359541149696,
    24371944523430924162076508160, 765279058035731018689202356224, 24371944523430924162076508160, 745781502416986279359541149696, 779902224749789573186448261120, 29246333428117108994491809792,
    410918721790290914999328047104, 306003303460854936701627269120, 323489206515760933084577398784, 419661673317743913190803111936, 5621717832152277837118466686976, 10168052626427836896685500399616,
    306003303460854936701627269120, 5621717832152277837118466686976, 332232158043213931276052463616, 332232158043213931276052463616, 323489206515760933084577398784, 323489206515760933084577398784,
    10168052626427836896685500399616, 323489206515760933084577398784, 410918721790290914999328047104, 419661673317743913190803111936, 33579123565615939956638744576, 823230126124777882807917608960,
    608757014318585750181644337152, 679164854052941753316532027392, 33579123565615939956638744576, 678081656518567045575995293696, 689996829396688830721899364352, 33579123565615939956638744576,
    823230126124777882807917608960
  ]
def positiveScales : Array ℕ := #[
    1, 6, 6, 5, 10, 6,
    5, 6, 6, 12, 4, 10,
    12, 6, 6, 4, 6, 7,
    12, 12, 8, 7, 8, 13,
    8, 7, 17, 13, 12, 13,
    8, 13, 8, 13, 8, 7,
    12, 11, 12, 8, 16, 17,
    11, 16, 11, 11, 12, 12,
    17, 12, 12, 8, 7, 9,
    10, 12, 7, 11, 12, 7,
    9
  ]
def negativeArguments : Array ℕ := #[
    3, 63, 113
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 19965496953594613073573075484672, 35811129456447480592281865551872
  ]
def negativeScales : Array ℕ := #[
    1, 5, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 6539158811107971, 6714245517659862, 5491853096329661, 10210671343785621, 6714245517659862,
    5491853096329661, 6714245517659862, 6714245517659862, 12087794304787900, 4754887502147955, 10210671343785621,
    12087794304787900, 6539158811107971, 6714245517659862, 4754887502147955, 6714245517659862, 7562242424220952,
    12420223419348643, 12244066464194817, 8299208018387278, 7562242424220952, 8299208018387278, 13234667766192568,
    8299208018387278, 7562242424220952, 17236434692366755, 13271900672391543, 12420223419348643, 13234667766192568,
    8299208018387278, 13271900672391543, 8299208018387278, 13234667766192568, 8299208018387278, 7562242424220952,
    12374767814092824, 11949461978722474, 12029632328044137, 8405141463136342, 16148853889743134, 17003814343888406,
    11949461978722474, 16148853889743134, 11068106475858773, 11068106475858773, 12029632328044137, 12029632328044137,
    17003814343888406, 12029632328044137, 12374767814092824, 8405141463136342, 7761551232426566, 9377210530388551,
    10941781241718677, 12099676554859642, 7761551232426566, 11097373768990222, 12122504484313904, 7761551232426566,
    9377210530388551
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 5977279939904027, 6820178963384638
  ]

abbrev PositiveTerm := Fin 61
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 12282528087 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2192738157 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 60847228810955011271841753858048, coefficient := 60847228810955011271841753858048 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 29246333428117108994491809792, coefficient := 29246333428117108994491809792 }, { argument := 424071834707698080420131241984, coefficient := 424071834707698080420131241984 }, { argument := 750655891321672464191956451328, coefficient := 750655891321672464191956451328 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 467941334849873743911868956672, coefficient := 467941334849873743911868956672 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 779902224749789573186448261120, coefficient := 779902224749789573186448261120 }, { argument := 467941334849873743911868956672, coefficient := 467941334849873743911868956672 }, { argument := 11947127205385839024249904300032, coefficient := 11947127205385839024249904300032 }, { argument := 765279058035731018689202356224, coefficient := 765279058035731018689202356224 }, { argument := 424071834707698080420131241984, coefficient := 424071834707698080420131241984 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 765279058035731018689202356224, coefficient := 765279058035731018689202356224 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 779902224749789573186448261120, coefficient := 779902224749789573186448261120 }, { argument := 29246333428117108994491809792, coefficient := 29246333428117108994491809792 }, { argument := 19965496953594613073573075484672, coefficient := (-19965496953594613073573075484672) }, { argument := 410918721790290914999328047104, coefficient := 410918721790290914999328047104 }, { argument := 306003303460854936701627269120, coefficient := 306003303460854936701627269120 }, { argument := 323489206515760933084577398784, coefficient := 323489206515760933084577398784 }, { argument := 419661673317743913190803111936, coefficient := 419661673317743913190803111936 }, { argument := 5621717832152277837118466686976, coefficient := 5621717832152277837118466686976 }, { argument := 10168052626427836896685500399616, coefficient := 10168052626427836896685500399616 }, { argument := 306003303460854936701627269120, coefficient := 306003303460854936701627269120 }, { argument := 5621717832152277837118466686976, coefficient := 5621717832152277837118466686976 }, { argument := 332232158043213931276052463616, coefficient := 332232158043213931276052463616 }, { argument := 332232158043213931276052463616, coefficient := 332232158043213931276052463616 }, { argument := 323489206515760933084577398784, coefficient := 323489206515760933084577398784 }, { argument := 323489206515760933084577398784, coefficient := 323489206515760933084577398784 }, { argument := 10168052626427836896685500399616, coefficient := 10168052626427836896685500399616 }, { argument := 323489206515760933084577398784, coefficient := 323489206515760933084577398784 }, { argument := 410918721790290914999328047104, coefficient := 410918721790290914999328047104 }, { argument := 419661673317743913190803111936, coefficient := 419661673317743913190803111936 }, { argument := 35811129456447480592281865551872, coefficient := (-35811129456447480592281865551872) }, { argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 823230126124777882807917608960, coefficient := 823230126124777882807917608960 }, { argument := 608757014318585750181644337152, coefficient := 608757014318585750181644337152 }, { argument := 679164854052941753316532027392, coefficient := 679164854052941753316532027392 }, { argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 678081656518567045575995293696, coefficient := 678081656518567045575995293696 }, { argument := 689996829396688830721899364352, coefficient := 689996829396688830721899364352 }, { argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 823230126124777882807917608960, coefficient := 823230126124777882807917608960 }] }

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

end TermShard7


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
