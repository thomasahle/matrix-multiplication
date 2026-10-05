import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 20, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5196451694592422270941917597401088)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    9458858565, 100598938557, 4729443537, 14682135, 37793919735, 1479063538953,
    1479063538953, 37793919735, 14613070875, 52562781375, 7306537875, 61580302785,
    2409942689343, 2409942689343, 61580302785, 1416298829205, 5094384770865, 708149650845,
    16164845689, 16164849543, 90601039425, 325889244525, 45300534825, 452221414763,
    452221522581, 20461438773303, 1812430215, 337149067565013, 18964208835, 839906685,
    674297935480839, 839906685, 1635607755, 30899724885, 1635607755, 18964208835,
    30899724885, 2557688165379, 1635607755, 1635607755, 1812430215, 51047051944297,
    145156375, 120272425, 5999375673659225, 808728375, 1633505402110855, 3239060825,
    3239060825, 2318354675, 120272425, 175687737379, 559217175, 175687740669,
    559217175, 46177303965, 166098389145, 23088659685, 16164845689, 16164849543,
    14587787573, 14587791051, 761685, 490710015
  ]
def negativeCoefficients : Array ℕ := #[
    43621285794492645906327797760, 463930718411952765520501014528, 43621417269049345252729552896, 135418793400326793807790080, 87146845611733214684742942720, 3410488321477641162474972512256,
    3410488321477641162474972512256, 87146845611733214684742942720, 269563578562103901929078784000, 969612175826972046841085952000, 269563668489981261263142912000, 283989021364109636664966512640,
    11113899005654411060932427907072, 11113899005654411060932427907072, 283989021364109636664966512640, 6531525508559777543741578936320, 23493703020287532694959512616960, 6531527687512245960405952757760,
    298188771415990143678020583424, 298188842509741803754632511488, 417823546771261047990072115200, 1502898872531806672603683225600, 417823686159470954957871513600, 521375793923994961583368306688,
    521375918229685745284395565056, 46075064017455804788867334144, 8358359081890844620735119360, 1518384415054102725986718056448, 87456976734906642495008931840, 7746771831996392575315476480,
    1518383965484100636975480963072, 7746771831996392575315476480, 7542909415364908560175595520, 284999658450814653165553582080, 7542909415364908560175595520, 87456976734906642495008931840,
    284999658450814653165553582080, 46075213874123167792613031936, 7542909415364908560175595520, 7542909415364908560175595520, 8358359081890844620735119360, 919581936458793290137493045248,
    42842600004678581047263232000, 2218634643099426518518988800, 3377348256043413015587140403200, 59673621435088023601545216000, 919581790031767351013943541760, 59750126077953521067701043200,
    59750126077953521067701043200, 42766095361813083581107404800, 2218634643099426518518988800, 202554170519969270164728315904, 10315736108847847225216204800, 202554174313081020321254866944,
    10315736108847847225216204800, 425910454128124165047944478720, 1531987237806615834008915804160, 425910596214170392795765800960, 298188771415990143678020583424, 298188842509741803754632511488,
    16818573997548224567205429248, 16818578007409217589819211776, 7025304129891729911316480, 2263000515277793794782658560
  ]
def negativeScales : Array ℕ := #[
    33, 36, 32, 23, 35, 40,
    40, 35, 33, 35, 32, 35,
    41, 41, 35, 40, 42, 39,
    33, 33, 36, 38, 35, 38,
    38, 44, 30, 48, 34, 29,
    49, 29, 30, 34, 30, 34,
    34, 41, 30, 30, 30, 45,
    27, 26, 52, 29, 50, 31,
    31, 31, 26, 37, 29, 37,
    29, 35, 37, 34, 33, 33,
    33, 33, 19, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33139018952776173, 36549824126772240, 32139023301052517, 23807558437638343, 35137435102004108, 40427821169018685,
    40427821169018685, 35137435102004108, 33766540335453724, 35613322567193292, 32766540816744567, 35841749911358503,
    41132135976894556, 41132135976894556, 35841749911358503, 40365262834808899, 42212045066861773, 39365263316099739,
    33912140689734014, 33912141033699349, 36398808550631795, 38245590782684664, 35398809031922635, 38718238355821326,
    38718238699786629, 44217972827207872, 30755278301552781, 48260379936110741, 34142560134181975, 29645653810145083,
    49260379508951122, 29645653810145083, 30607179662318269, 34846874943689492, 30607179662318269, 34142560134181975,
    34846874943689492, 41217977519488260, 30607179662318269, 30607179662318269, 30755278301552781, 45536892878906986,
    27113032692957522, 26841730672618084, 52413733797468182, 29591079989766576, 50536892649183508, 31592928414159179,
    31592928414159179, 31110454148855746, 26841730672618084, 37354222541653121, 29058833429373802, 37354222568669615,
    29058833429373802, 35426464893534673, 37273247125587529, 34426465374825513, 33912140689734014, 33912141033699349,
    33764042045628651, 33764042389593955, 19538834959170594, 28870295477599567
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
noncomputable def negativeCeiling : ℝ := 10612525921 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 43621285794492645906327797760, coefficient := (-43621285794492645906327797760) }, { argument := 463930718411952765520501014528, coefficient := (-463930718411952765520501014528) }, { argument := 43621417269049345252729552896, coefficient := (-43621417269049345252729552896) }, { argument := 135418793400326793807790080, coefficient := (-135418793400326793807790080) }, { argument := 87146845611733214684742942720, coefficient := (-87146845611733214684742942720) }, { argument := 3410488321477641162474972512256, coefficient := (-3410488321477641162474972512256) }, { argument := 3410488321477641162474972512256, coefficient := (-3410488321477641162474972512256) }, { argument := 87146845611733214684742942720, coefficient := (-87146845611733214684742942720) }, { argument := 269563578562103901929078784000, coefficient := (-269563578562103901929078784000) }, { argument := 969612175826972046841085952000, coefficient := (-969612175826972046841085952000) }, { argument := 269563668489981261263142912000, coefficient := (-269563668489981261263142912000) }, { argument := 283989021364109636664966512640, coefficient := (-283989021364109636664966512640) }, { argument := 11113899005654411060932427907072, coefficient := (-11113899005654411060932427907072) }, { argument := 11113899005654411060932427907072, coefficient := (-11113899005654411060932427907072) }, { argument := 283989021364109636664966512640, coefficient := (-283989021364109636664966512640) }, { argument := 6531525508559777543741578936320, coefficient := (-6531525508559777543741578936320) }, { argument := 23493703020287532694959512616960, coefficient := (-23493703020287532694959512616960) }, { argument := 6531527687512245960405952757760, coefficient := (-6531527687512245960405952757760) }, { argument := 298188771415990143678020583424, coefficient := (-298188771415990143678020583424) }, { argument := 298188842509741803754632511488, coefficient := (-298188842509741803754632511488) }, { argument := 417823546771261047990072115200, coefficient := (-417823546771261047990072115200) }, { argument := 1502898872531806672603683225600, coefficient := (-1502898872531806672603683225600) }, { argument := 417823686159470954957871513600, coefficient := (-417823686159470954957871513600) }, { argument := 521375793923994961583368306688, coefficient := (-521375793923994961583368306688) }, { argument := 521375918229685745284395565056, coefficient := (-521375918229685745284395565056) }, { argument := 46075064017455804788867334144, coefficient := (-46075064017455804788867334144) }, { argument := 8358359081890844620735119360, coefficient := (-8358359081890844620735119360) }, { argument := 1518384415054102725986718056448, coefficient := (-1518384415054102725986718056448) }, { argument := 87456976734906642495008931840, coefficient := (-87456976734906642495008931840) }, { argument := 7746771831996392575315476480, coefficient := (-7746771831996392575315476480) }, { argument := 1518383965484100636975480963072, coefficient := (-1518383965484100636975480963072) }, { argument := 7746771831996392575315476480, coefficient := (-7746771831996392575315476480) }, { argument := 7542909415364908560175595520, coefficient := (-7542909415364908560175595520) }, { argument := 284999658450814653165553582080, coefficient := (-284999658450814653165553582080) }, { argument := 7542909415364908560175595520, coefficient := (-7542909415364908560175595520) }, { argument := 87456976734906642495008931840, coefficient := (-87456976734906642495008931840) }, { argument := 284999658450814653165553582080, coefficient := (-284999658450814653165553582080) }, { argument := 46075213874123167792613031936, coefficient := (-46075213874123167792613031936) }, { argument := 7542909415364908560175595520, coefficient := (-7542909415364908560175595520) }, { argument := 7542909415364908560175595520, coefficient := (-7542909415364908560175595520) }, { argument := 8358359081890844620735119360, coefficient := (-8358359081890844620735119360) }, { argument := 919581936458793290137493045248, coefficient := (-919581936458793290137493045248) }, { argument := 42842600004678581047263232000, coefficient := (-42842600004678581047263232000) }, { argument := 2218634643099426518518988800, coefficient := (-2218634643099426518518988800) }, { argument := 3377348256043413015587140403200, coefficient := (-3377348256043413015587140403200) }, { argument := 59673621435088023601545216000, coefficient := (-59673621435088023601545216000) }, { argument := 919581790031767351013943541760, coefficient := (-919581790031767351013943541760) }, { argument := 59750126077953521067701043200, coefficient := (-59750126077953521067701043200) }, { argument := 59750126077953521067701043200, coefficient := (-59750126077953521067701043200) }, { argument := 42766095361813083581107404800, coefficient := (-42766095361813083581107404800) }, { argument := 2218634643099426518518988800, coefficient := (-2218634643099426518518988800) }, { argument := 202554170519969270164728315904, coefficient := (-202554170519969270164728315904) }, { argument := 10315736108847847225216204800, coefficient := (-10315736108847847225216204800) }, { argument := 202554174313081020321254866944, coefficient := (-202554174313081020321254866944) }, { argument := 10315736108847847225216204800, coefficient := (-10315736108847847225216204800) }, { argument := 425910454128124165047944478720, coefficient := (-425910454128124165047944478720) }, { argument := 1531987237806615834008915804160, coefficient := (-1531987237806615834008915804160) }, { argument := 425910596214170392795765800960, coefficient := (-425910596214170392795765800960) }, { argument := 298188771415990143678020583424, coefficient := (-298188771415990143678020583424) }, { argument := 298188842509741803754632511488, coefficient := (-298188842509741803754632511488) }, { argument := 16818573997548224567205429248, coefficient := (-16818573997548224567205429248) }, { argument := 16818578007409217589819211776, coefficient := (-16818578007409217589819211776) }, { argument := 7025304129891729911316480, coefficient := (-7025304129891729911316480) }, { argument := 2263000515277793794782658560, coefficient := (-2263000515277793794782658560) }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 53698170910773896224245207688806400
def positiveArguments : Array ℕ := #[
    7105, 285, 855, 1805, 4655, 3895,
    108965, 3325
  ]
def positiveCoefficients : Array ℕ := #[
    562916094663848118602129767137280, 88203227799083344586562600960, 66152420849312508439921950720, 69827555340940981131028725760, 90040795044897580932115988480, 1205444113254139042683022213120,
    2107689630948929088349735485440, 64314853603498272094368563200
  ]
def positiveScales : Array ℕ := #[
    12, 8, 9, 10, 12, 11,
    16, 11
  ]
def negativeArguments : Array ℕ := #[
    5218907367, 245355747, 761685, 3259615455, 127564920609, 127564920609,
    3259615455, 1753568505, 6307533765, 876784545, 3259615455, 127564920609,
    127564920609, 3259615455, 90601039425, 325889244525, 45300534825, 7491026051,
    7491027837, 1753568505, 6307533765, 876784545, 7491026051, 7491027837,
    3612006315, 141355722837, 141355722837, 3612006315, 46177303965, 166098389145,
    23088659685, 14587787573, 14587791051, 46177303965, 166098389145, 23088659685,
    452221414763, 452221522581, 14587787573, 14587791051, 75946244111, 450625,
    373375, 8787937489535, 2510625, 2430280197025, 10055375, 10055375,
    7197125, 373375, 620072581, 2819561, 310036361, 2819561,
    19318961921, 19318966527
  ]
def negativeCoefficients : Array ℕ := #[
    24067962135861592486752288768, 2263007335961415048889368576, 7025304129891729911316480, 7516161509636664203579228160, 294144680407162524502503456768, 294144680407162524502503456768,
    7516161509636664203579228160, 16173814713726234115744727040, 58176730549618322810465157120, 16173820109398875675788574720, 7516161509636664203579228160, 294144680407162524502503456768,
    294144680407162524502503456768, 7516161509636664203579228160, 417823546771261047990072115200, 1502898872531806672603683225600, 417823686159470954957871513600, 17273130051536014420373143552,
    17273134169771628876030541824, 16173814713726234115744727040, 58176730549618322810465157120, 16173820109398875675788574720, 17273130051536014420373143552, 17273134169771628876030541824,
    8328719510678465739101306880, 325944105316044959583855181824, 325944105316044959583855181824, 8328719510678465739101306880, 425910454128124165047944478720, 1531987237806615834008915804160,
    425910596214170392795765800960, 16818573997548224567205429248, 16818578007409217589819211776, 425910454128124165047944478720, 1531987237806615834008915804160, 425910596214170392795765800960,
    521375793923994961583368306688, 521375918229685745284395565056, 16818573997548224567205429248, 16818578007409217589819211776, 21890014507423252880329539584, 133001024771445867151360000,
    6887553068521303834624000, 79154704006450076183135518720, 185251427360228172103680000, 21890017979455371203103948800, 185488929190177182580736000, 185488929190177182580736000,
    132763522941496856674304000, 6887553068521303834624000, 22876640417663071829771681792, 52011720167212577063960576, 22876645619644900615865237504, 52011720167212577063960576,
    22273246645401702805218000896, 22273251955758153024355172352
  ]
def negativeScales : Array ℕ := #[
    32, 27, 19, 31, 36, 36,
    31, 30, 32, 29, 31, 36,
    36, 31, 36, 38, 35, 32,
    32, 30, 32, 29, 32, 32,
    31, 37, 37, 31, 35, 37,
    34, 33, 33, 35, 37, 34,
    38, 38, 33, 33, 36, 18,
    18, 42, 21, 41, 23, 23,
    22, 18, 29, 21, 28, 21,
    34, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12794618934094284, 8154818109052103, 9739780609762119, 10817783121717284, 12184565452446155, 11927407612511617,
    16733505284337084, 11699138625271509
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32281100649055299, 27870299825876117, 19538834959170594, 31602054630139497, 36892440700959720, 36892440700959720,
    31602054630139497, 30707646646165271, 32554428878133102, 29707647127456111, 31602054630139497, 36892440700959720,
    36892440700959720, 31602054630139497, 36398808550631795, 38245590782684664, 35398809031922635, 32802516193818542,
    32802516537783848, 30707646646165271, 32554428878133102, 29707647127456111, 32802516193818542, 32802516537783848,
    31750153269348281, 37040539336137203, 37040539336137203, 31750153269348281, 35426464893534673, 37273247125587529,
    34426465374825513, 33764042045628651, 33764042389593955, 35426464893534673, 37273247125587529, 34426465374825513,
    38718238355821326, 38718238699786629, 33764042045628651, 33764042389593955, 36144259567499343, 18781567829231832,
    18510265806973259, 42998661769426120, 21259615125594917, 41144259796328936, 23261463549987285, 23261463549987285,
    22778989285106841, 18510265806973259, 29207861855437303, 21427039124705171, 28207862183495637, 21427039124705171,
    34169298523810185, 34169298867775487
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
noncomputable def positiveFloor : ℝ := 17467973439 / 200000000000
noncomputable def negativeCeiling : ℝ := 1172595833 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24067962135861592486752288768, coefficient := (-24067962135861592486752288768) }, { argument := 2263007335961415048889368576, coefficient := (-2263007335961415048889368576) }, { argument := 7025304129891729911316480, coefficient := (-7025304129891729911316480) }, { argument := 7516161509636664203579228160, coefficient := (-7516161509636664203579228160) }, { argument := 294144680407162524502503456768, coefficient := (-294144680407162524502503456768) }, { argument := 294144680407162524502503456768, coefficient := (-294144680407162524502503456768) }, { argument := 7516161509636664203579228160, coefficient := (-7516161509636664203579228160) }, { argument := 16173814713726234115744727040, coefficient := (-16173814713726234115744727040) }, { argument := 58176730549618322810465157120, coefficient := (-58176730549618322810465157120) }, { argument := 16173820109398875675788574720, coefficient := (-16173820109398875675788574720) }, { argument := 7516161509636664203579228160, coefficient := (-7516161509636664203579228160) }, { argument := 294144680407162524502503456768, coefficient := (-294144680407162524502503456768) }, { argument := 294144680407162524502503456768, coefficient := (-294144680407162524502503456768) }, { argument := 7516161509636664203579228160, coefficient := (-7516161509636664203579228160) }, { argument := 417823546771261047990072115200, coefficient := (-417823546771261047990072115200) }, { argument := 1502898872531806672603683225600, coefficient := (-1502898872531806672603683225600) }, { argument := 417823686159470954957871513600, coefficient := (-417823686159470954957871513600) }, { argument := 17273130051536014420373143552, coefficient := (-17273130051536014420373143552) }, { argument := 17273134169771628876030541824, coefficient := (-17273134169771628876030541824) }, { argument := 16173814713726234115744727040, coefficient := (-16173814713726234115744727040) }, { argument := 58176730549618322810465157120, coefficient := (-58176730549618322810465157120) }, { argument := 16173820109398875675788574720, coefficient := (-16173820109398875675788574720) }, { argument := 17273130051536014420373143552, coefficient := (-17273130051536014420373143552) }, { argument := 17273134169771628876030541824, coefficient := (-17273134169771628876030541824) }, { argument := 8328719510678465739101306880, coefficient := (-8328719510678465739101306880) }, { argument := 325944105316044959583855181824, coefficient := (-325944105316044959583855181824) }, { argument := 325944105316044959583855181824, coefficient := (-325944105316044959583855181824) }, { argument := 8328719510678465739101306880, coefficient := (-8328719510678465739101306880) }, { argument := 425910454128124165047944478720, coefficient := (-425910454128124165047944478720) }, { argument := 1531987237806615834008915804160, coefficient := (-1531987237806615834008915804160) }, { argument := 425910596214170392795765800960, coefficient := (-425910596214170392795765800960) }, { argument := 16818573997548224567205429248, coefficient := (-16818573997548224567205429248) }, { argument := 16818578007409217589819211776, coefficient := (-16818578007409217589819211776) }, { argument := 425910454128124165047944478720, coefficient := (-425910454128124165047944478720) }, { argument := 1531987237806615834008915804160, coefficient := (-1531987237806615834008915804160) }, { argument := 425910596214170392795765800960, coefficient := (-425910596214170392795765800960) }, { argument := 521375793923994961583368306688, coefficient := (-521375793923994961583368306688) }, { argument := 521375918229685745284395565056, coefficient := (-521375918229685745284395565056) }, { argument := 16818573997548224567205429248, coefficient := (-16818573997548224567205429248) }, { argument := 16818578007409217589819211776, coefficient := (-16818578007409217589819211776) }, { argument := 21890014507423252880329539584, coefficient := (-21890014507423252880329539584) }, { argument := 133001024771445867151360000, coefficient := (-133001024771445867151360000) }, { argument := 6887553068521303834624000, coefficient := (-6887553068521303834624000) }, { argument := 79154704006450076183135518720, coefficient := (-79154704006450076183135518720) }, { argument := 185251427360228172103680000, coefficient := (-185251427360228172103680000) }, { argument := 21890017979455371203103948800, coefficient := (-21890017979455371203103948800) }, { argument := 185488929190177182580736000, coefficient := (-185488929190177182580736000) }, { argument := 185488929190177182580736000, coefficient := (-185488929190177182580736000) }, { argument := 132763522941496856674304000, coefficient := (-132763522941496856674304000) }, { argument := 6887553068521303834624000, coefficient := (-6887553068521303834624000) }, { argument := 22876640417663071829771681792, coefficient := (-22876640417663071829771681792) }, { argument := 52011720167212577063960576, coefficient := (-52011720167212577063960576) }, { argument := 22876645619644900615865237504, coefficient := (-22876645619644900615865237504) }, { argument := 52011720167212577063960576, coefficient := (-52011720167212577063960576) }, { argument := 22273246645401702805218000896, coefficient := (-22273246645401702805218000896) }, { argument := 22273251955758153024355172352, coefficient := (-22273251955758153024355172352) }, { argument := 562916094663848118602129767137280, coefficient := 562916094663848118602129767137280 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 66152420849312508439921950720, coefficient := 66152420849312508439921950720 }, { argument := 69827555340940981131028725760, coefficient := 69827555340940981131028725760 }, { argument := 90040795044897580932115988480, coefficient := 90040795044897580932115988480 }, { argument := 1205444113254139042683022213120, coefficient := 1205444113254139042683022213120 }, { argument := 2107689630948929088349735485440, coefficient := 2107689630948929088349735485440 }, { argument := 64314853603498272094368563200, coefficient := 64314853603498272094368563200 }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20
