import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6840386086238611800907061412233216)
def positiveArguments : Array ℕ := #[
    1, 3499807, 94998033, 27998455, 53556249, 141,
    938956239, 3489, 111, 1877913241, 57, 57,
    1929, 105, 3489, 1929, 3347227, 111,
    105, 141, 26494779, 2616969927, 2295, 26149312445,
    2355, 75, 2295, 1305, 2355, 36765,
    45, 1308485507, 2295, 75, 45, 75,
    1155, 1305, 26494779, 241236195, 11113502493, 26845,
    23777, 1112917, 302965, 5556752637, 1112917, 26845,
    26845, 11505, 26845, 302965, 11505, 120616707,
    23777, 120879907, 78657, 777977053, 126699
  ]
def positiveCoefficients : Array ℕ := #[
    79228162514264337593543950336, 264437940373001030502556106752, 897231053955488981417969319936, 264437930928268064763265679360, 252912235225820953606361186304, 5454673298101206836274266112,
    8868190943869879994232694898688, 134974149908334118097595138048, 4294104511271162828556337152, 8868194547035506423771992948736, 4410161389954167229328130048, 4410161389954167229328130048,
    74624572993171829696262832128, 4061990753905154027012751360, 134974149908334118097595138048, 74624572993171829696262832128, 252909321525701023035264335872, 4294104511271162828556337152,
    4061990753905154027012751360, 5454673298101206836274266112, 125118056320638535745283293184, 12358291069942622185401920520192, 710268097539986932723372523520, 123486636640354092899235497246720,
    728837198129267636846859386880, 23211375736600880154358579200, 710268097539986932723372523520, 403877937816855314685839278080, 728837198129267636846859386880, 11378216386081751451666575523840,
    445658414142736898963684720640, 12358296203154989064706267807744, 710268097539986932723372523520, 23211375736600880154358579200, 445658414142736898963684720640, 23211375736600880154358579200,
    714910372687307108754244239360, 403877937816855314685839278080, 125118056320638535745283293184, 1139205721723005892351984926720, 52482031680231443876436013744128, 519257818040875523119796715520,
    459914067407632606191819948032, 21526945542208868115623572406272, 5860195375032738046637705789440, 52482044813132632736919353032704, 21526945542208868115623572406272, 519257818040875523119796715520,
    519257818040875523119796715520, 445078129749321876959825756160, 519257818040875523119796715520, 5860195375032738046637705789440, 445078129749321876959825756160, 1139192588821817031868645638144,
    459914067407632606191819948032, 570839221269199806554567606272, 1521447651094846191917818970112, 7347785519057803133013538635776, 2450715078709662428897564688384
  ]
def positiveScales : Array ℕ := #[
    0, 21, 26, 24, 25, 7,
    29, 11, 6, 30, 5, 5,
    10, 6, 11, 10, 21, 6,
    6, 7, 24, 31, 11, 34,
    11, 6, 11, 10, 11, 15,
    5, 30, 11, 6, 5, 6,
    10, 10, 24, 27, 33, 14,
    14, 20, 18, 32, 20, 14,
    14, 13, 14, 18, 13, 26,
    14, 26, 16, 29, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 9, 59, 1047, 1047
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 1426106925256758076683791106048, 18697846353366383672076372279296, 165903772304869522920881032003584, 165903772304869522920881032003584
  ]
def negativeScales : Array ℕ := #[
    0, 3, 5, 10, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 21738843934850818, 26501394305965373, 24738843883323153, 25674551584195395, 7139551352398793,
    29806482680245538, 11768597882173550, 6794415866314396, 30806483266415609, 5832890014087662, 5832890014087662,
    10913637427705176, 6714245517659862, 11768597882173550, 10913637427705176, 21674534963390460, 6794415866314396,
    6714245517659862, 7139551352398793, 24659204757738169, 31285250199687741, 11164278438301170, 34606053962449463,
    11201511344500145, 6228818690495880, 11164278438301170, 10349834091457246, 11201511344500145, 15166045364475357,
    5491853096329661, 30285250798933903, 11164278438301170, 6228818690495880, 5491853096329661, 6228818690495880,
    10173677136303419, 10349834091457246, 24659204757738169, 27845871143971654, 33371594512040823, 14712365784441905,
    14537279077889752, 20085914571569677, 18208791610567398, 32371594873055221, 20085914571569677, 14712365784441905,
    14712365784441905, 13489973363111439, 14712365784441905, 18208791610567398, 13489973363111439, 26845854512313095,
    14537279077889752, 26848999214659652, 16263287542086835, 29535152361596515, 16951045611514478
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 3169925001442313, 5882643052550791, 10032045726930809, 10032045726930809
  ]

abbrev PositiveTerm := Fin 59
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 130122127739 / 1000000000000
noncomputable def negativeCeiling : ℝ := 4144627563 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 264437940373001030502556106752, coefficient := 264437940373001030502556106752 }, { argument := 897231053955488981417969319936, coefficient := 897231053955488981417969319936 }, { argument := 264437930928268064763265679360, coefficient := 264437930928268064763265679360 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 252912235225820953606361186304, coefficient := 252912235225820953606361186304 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 8868190943869879994232694898688, coefficient := 8868190943869879994232694898688 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 8868194547035506423771992948736, coefficient := 8868194547035506423771992948736 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 252909321525701023035264335872, coefficient := 252909321525701023035264335872 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 18697846353366383672076372279296, coefficient := (-18697846353366383672076372279296) }, { argument := 125118056320638535745283293184, coefficient := 125118056320638535745283293184 }, { argument := 12358291069942622185401920520192, coefficient := 12358291069942622185401920520192 }, { argument := 710268097539986932723372523520, coefficient := 710268097539986932723372523520 }, { argument := 123486636640354092899235497246720, coefficient := 123486636640354092899235497246720 }, { argument := 728837198129267636846859386880, coefficient := 728837198129267636846859386880 }, { argument := 23211375736600880154358579200, coefficient := 23211375736600880154358579200 }, { argument := 710268097539986932723372523520, coefficient := 710268097539986932723372523520 }, { argument := 403877937816855314685839278080, coefficient := 403877937816855314685839278080 }, { argument := 728837198129267636846859386880, coefficient := 728837198129267636846859386880 }, { argument := 11378216386081751451666575523840, coefficient := 11378216386081751451666575523840 }, { argument := 445658414142736898963684720640, coefficient := 445658414142736898963684720640 }, { argument := 12358296203154989064706267807744, coefficient := 12358296203154989064706267807744 }, { argument := 710268097539986932723372523520, coefficient := 710268097539986932723372523520 }, { argument := 23211375736600880154358579200, coefficient := 23211375736600880154358579200 }, { argument := 445658414142736898963684720640, coefficient := 445658414142736898963684720640 }, { argument := 23211375736600880154358579200, coefficient := 23211375736600880154358579200 }, { argument := 714910372687307108754244239360, coefficient := 714910372687307108754244239360 }, { argument := 403877937816855314685839278080, coefficient := 403877937816855314685839278080 }, { argument := 125118056320638535745283293184, coefficient := 125118056320638535745283293184 }, { argument := 165903772304869522920881032003584, coefficient := (-165903772304869522920881032003584) }, { argument := 1139205721723005892351984926720, coefficient := 1139205721723005892351984926720 }, { argument := 52482031680231443876436013744128, coefficient := 52482031680231443876436013744128 }, { argument := 519257818040875523119796715520, coefficient := 519257818040875523119796715520 }, { argument := 459914067407632606191819948032, coefficient := 459914067407632606191819948032 }, { argument := 21526945542208868115623572406272, coefficient := 21526945542208868115623572406272 }, { argument := 5860195375032738046637705789440, coefficient := 5860195375032738046637705789440 }, { argument := 52482044813132632736919353032704, coefficient := 52482044813132632736919353032704 }, { argument := 21526945542208868115623572406272, coefficient := 21526945542208868115623572406272 }, { argument := 519257818040875523119796715520, coefficient := 519257818040875523119796715520 }, { argument := 519257818040875523119796715520, coefficient := 519257818040875523119796715520 }, { argument := 445078129749321876959825756160, coefficient := 445078129749321876959825756160 }, { argument := 519257818040875523119796715520, coefficient := 519257818040875523119796715520 }, { argument := 5860195375032738046637705789440, coefficient := 5860195375032738046637705789440 }, { argument := 445078129749321876959825756160, coefficient := 445078129749321876959825756160 }, { argument := 1139192588821817031868645638144, coefficient := 1139192588821817031868645638144 }, { argument := 459914067407632606191819948032, coefficient := 459914067407632606191819948032 }, { argument := 165903772304869522920881032003584, coefficient := (-165903772304869522920881032003584) }, { argument := 570839221269199806554567606272, coefficient := 570839221269199806554567606272 }, { argument := 1521447651094846191917818970112, coefficient := 1521447651094846191917818970112 }, { argument := 7347785519057803133013538635776, coefficient := 7347785519057803133013538635776 }, { argument := 2450715078709662428897564688384, coefficient := 2450715078709662428897564688384 }] }

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

end TermShard10


end Parent0

namespace Parent0

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1256330371366905944662816394838016)
def positiveArguments : Array ℕ := #[
    3925, 126699, 84623, 121522979, 78657, 471,
    535, 489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    75920541471798712171547852800, 2450715078709662428897564688384, 1636846874131980234418571706368, 573876042928071755041429520384, 1521447651094846191917818970112, 72883719812926763684685938688,
    331148960508839223535515729920, 302676339605275477212835872768, 331148960508839223535515729920, 302676339605275477212835872768
  ]
def positiveScales : Array ℕ := #[
    11, 16, 16, 26, 16, 8,
    9, 8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    115, 1
  ]
def negativeCoefficients : Array ℕ := #[
    18222477378280797646515108577280, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    6, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11938476938137180, 16951045611514478, 16368762211644132, 26856653900419771, 16263287542086835, 8879583249426338,
    9063395081288509, 8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6845490052533228, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 1461970113 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1501524651 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 75920541471798712171547852800, coefficient := 75920541471798712171547852800 }, { argument := 2450715078709662428897564688384, coefficient := 2450715078709662428897564688384 }, { argument := 1636846874131980234418571706368, coefficient := 1636846874131980234418571706368 }, { argument := 573876042928071755041429520384, coefficient := 573876042928071755041429520384 }, { argument := 1521447651094846191917818970112, coefficient := 1521447651094846191917818970112 }, { argument := 72883719812926763684685938688, coefficient := 72883719812926763684685938688 }, { argument := 18222477378280797646515108577280, coefficient := (-18222477378280797646515108577280) }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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

end TermShard11


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
