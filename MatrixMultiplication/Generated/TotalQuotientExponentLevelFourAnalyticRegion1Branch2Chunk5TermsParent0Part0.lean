import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1375120658924729687871750720716800)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    627671, 17021993, 105, 93, 4353, 1185,
    8510997, 4353, 105, 105, 45, 105,
    1185, 45, 313835, 93, 30122284876141, 1122810615452935,
    19431, 4584684609359805, 19939, 635, 19431, 11049,
    19939, 311277, 381, 561405454560305, 19431, 635,
    381, 635, 9779, 11049, 30122284876141, 37323421419231,
    1719050427, 407065593597597, 42537354183, 1353295017, 407065790250347, 694935279,
    694935279, 23518072863, 1280143935, 42537354183, 23518072863, 37323223933201,
    1353295017, 1280143935, 1719050427, 16272221, 1201660943, 12524711045,
    1201660943, 16272221, 93622025, 3392893175, 27143155375, 748966225,
    38108479678219, 24074235, 7855803, 1056527172593305
  ]
def negativeCoefficients : Array ℕ := #[
    2964092492669273080925782016, 80384089214841720740016816128, 2030995376952577013506375680, 1798881619586568211962789888, 84199265484519692759935746048, 22921233539893369152429096960,
    80384093937208203609662029824, 84199265484519692759935746048, 2030995376952577013506375680, 2030995376952577013506375680, 1740853180245066011576893440, 2030995376952577013506375680,
    22921233539893369152429096960, 1740853180245066011576893440, 2964087770302790211280568320, 1798881619586568211962789888, 8478669433983533428554858496, 316043091835092208989880975360,
    187925100807454875949725646848, 1290473993645254113488881582080, 192838175338368728915731546112, 6141343163642316207507374080, 187925100807454875949725646848, 106859371047376302010628308992,
    192838175338368728915731546112, 3010486418817463404920114774016, 117913788741932471184141582336, 316043174495194190287376220160, 187925100807454875949725646848, 6141343163642316207507374080,
    117913788741932471184141582336, 6141343163642316207507374080, 189153369440183339191227121664, 106859371047376302010628308992, 8478669433983533428554858496, 168089746795840720568976408576,
    63421766553340248358926680064, 3666520911282975222923708596224, 1569351372373078911519824019456, 49927773669650833814474194944, 3666522682573478465690323124224, 51277172958019775268919443456,
    51277172958019775268919443456, 867663742421229355208294793216, 47228975092912950905583697920, 1569351372373078911519824019456, 867663742421229355208294793216, 168088857397829601690382237696,
    49927773669650833814474194944, 47228975092912950905583697920, 63421766553340248358926680064, 75042374074460528426614784, 11083365939446740651494866944, 115520069622139157623456399360,
    11083365939446740651494866944, 75042374074460528426614784, 13816172278699499873055539200, 500702656549286676881892966400, 500702840555558812134670336000, 13815988272427364620278169600,
    171625334878483207711174426624, 14210920058090914155142840320, 579655949737918866854510592, 594771922599751514004295516160
  ]
def negativeScales : Array ℕ := #[
    19, 24, 6, 6, 12, 10,
    23, 12, 6, 6, 5, 6,
    10, 5, 18, 6, 44, 49,
    14, 52, 14, 9, 14, 13,
    14, 18, 8, 48, 14, 9,
    8, 9, 13, 13, 44, 45,
    30, 48, 35, 30, 48, 29,
    29, 34, 30, 35, 34, 45,
    30, 30, 30, 23, 30, 33,
    30, 23, 26, 31, 34, 29,
    45, 24, 22, 49
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19259649028709589, 24020896627374360, 6714245517766967, 6539158811108986, 12087794304787901, 10210671343785622,
    23020896712129124, 12087794304787901, 6714245517766967, 6714245517766967, 5491853096329881, 6714245517766967,
    10210671343785622, 5491853096329881, 18259646730218516, 6539158811108986, 44775896441336422, 49996036054315808,
    14246072529464818, 52025743914347155, 14283305435663794, 9310612781659529, 14246072529464818, 13431628182620918,
    14283305435663794, 18247839455639006, 8573647187496003, 48996036431648359, 14246072529464818, 9310612781659529,
    8573647187496003, 9310612781659529, 13255471227467068, 13431628182620918, 44775896441336422, 45085146476914750,
    30678964719797598, 48532254614151738, 35308011249549401, 30333829233705132, 48532255311115282, 29372303381519770,
    29372303381519770, 34453050795404182, 30253658885021149, 35308011249549401, 34453050795404182, 45085138843293312,
    30333829233705132, 30253658885021149, 30678964719797598, 23955907854025280, 30162382741004284, 33544058268562338,
    30162382741004284, 23955907854025280, 26480344634408549, 31659868861626916, 34659869391811616, 29480325420208065,
    45115177287121504, 24520986618906294, 22905327325765521, 49908251300481616
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
noncomputable def negativeCeiling : ℝ := 9779911999 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2964092492669273080925782016, coefficient := (-2964092492669273080925782016) }, { argument := 80384089214841720740016816128, coefficient := (-80384089214841720740016816128) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 84199265484519692759935746048, coefficient := (-84199265484519692759935746048) }, { argument := 22921233539893369152429096960, coefficient := (-22921233539893369152429096960) }, { argument := 80384093937208203609662029824, coefficient := (-80384093937208203609662029824) }, { argument := 84199265484519692759935746048, coefficient := (-84199265484519692759935746048) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 22921233539893369152429096960, coefficient := (-22921233539893369152429096960) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 2964087770302790211280568320, coefficient := (-2964087770302790211280568320) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 8478669433983533428554858496, coefficient := (-8478669433983533428554858496) }, { argument := 316043091835092208989880975360, coefficient := (-316043091835092208989880975360) }, { argument := 187925100807454875949725646848, coefficient := (-187925100807454875949725646848) }, { argument := 1290473993645254113488881582080, coefficient := (-1290473993645254113488881582080) }, { argument := 192838175338368728915731546112, coefficient := (-192838175338368728915731546112) }, { argument := 6141343163642316207507374080, coefficient := (-6141343163642316207507374080) }, { argument := 187925100807454875949725646848, coefficient := (-187925100807454875949725646848) }, { argument := 106859371047376302010628308992, coefficient := (-106859371047376302010628308992) }, { argument := 192838175338368728915731546112, coefficient := (-192838175338368728915731546112) }, { argument := 3010486418817463404920114774016, coefficient := (-3010486418817463404920114774016) }, { argument := 117913788741932471184141582336, coefficient := (-117913788741932471184141582336) }, { argument := 316043174495194190287376220160, coefficient := (-316043174495194190287376220160) }, { argument := 187925100807454875949725646848, coefficient := (-187925100807454875949725646848) }, { argument := 6141343163642316207507374080, coefficient := (-6141343163642316207507374080) }, { argument := 117913788741932471184141582336, coefficient := (-117913788741932471184141582336) }, { argument := 6141343163642316207507374080, coefficient := (-6141343163642316207507374080) }, { argument := 189153369440183339191227121664, coefficient := (-189153369440183339191227121664) }, { argument := 106859371047376302010628308992, coefficient := (-106859371047376302010628308992) }, { argument := 8478669433983533428554858496, coefficient := (-8478669433983533428554858496) }, { argument := 168089746795840720568976408576, coefficient := (-168089746795840720568976408576) }, { argument := 63421766553340248358926680064, coefficient := (-63421766553340248358926680064) }, { argument := 3666520911282975222923708596224, coefficient := (-3666520911282975222923708596224) }, { argument := 1569351372373078911519824019456, coefficient := (-1569351372373078911519824019456) }, { argument := 49927773669650833814474194944, coefficient := (-49927773669650833814474194944) }, { argument := 3666522682573478465690323124224, coefficient := (-3666522682573478465690323124224) }, { argument := 51277172958019775268919443456, coefficient := (-51277172958019775268919443456) }, { argument := 51277172958019775268919443456, coefficient := (-51277172958019775268919443456) }, { argument := 867663742421229355208294793216, coefficient := (-867663742421229355208294793216) }, { argument := 47228975092912950905583697920, coefficient := (-47228975092912950905583697920) }, { argument := 1569351372373078911519824019456, coefficient := (-1569351372373078911519824019456) }, { argument := 867663742421229355208294793216, coefficient := (-867663742421229355208294793216) }, { argument := 168088857397829601690382237696, coefficient := (-168088857397829601690382237696) }, { argument := 49927773669650833814474194944, coefficient := (-49927773669650833814474194944) }, { argument := 47228975092912950905583697920, coefficient := (-47228975092912950905583697920) }, { argument := 63421766553340248358926680064, coefficient := (-63421766553340248358926680064) }, { argument := 75042374074460528426614784, coefficient := (-75042374074460528426614784) }, { argument := 11083365939446740651494866944, coefficient := (-11083365939446740651494866944) }, { argument := 115520069622139157623456399360, coefficient := (-115520069622139157623456399360) }, { argument := 11083365939446740651494866944, coefficient := (-11083365939446740651494866944) }, { argument := 75042374074460528426614784, coefficient := (-75042374074460528426614784) }, { argument := 13816172278699499873055539200, coefficient := (-13816172278699499873055539200) }, { argument := 500702656549286676881892966400, coefficient := (-500702656549286676881892966400) }, { argument := 500702840555558812134670336000, coefficient := (-500702840555558812134670336000) }, { argument := 13815988272427364620278169600, coefficient := (-13815988272427364620278169600) }, { argument := 171625334878483207711174426624, coefficient := (-171625334878483207711174426624) }, { argument := 14210920058090914155142840320, coefficient := (-14210920058090914155142840320) }, { argument := 579655949737918866854510592, coefficient := (-579655949737918866854510592) }, { argument := 594771922599751514004295516160, coefficient := (-594771922599751514004295516160) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4268117998641380406644782370127872)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    79318269, 304867777536271, 158889951, 71209053, 24074235, 7855803,
    30550345, 1107154615, 8857240175, 244399505, 14154734367, 23990363361,
    14154734367, 14802530765855, 16272221, 14801724347361, 8216033, 30120624602771,
    1122636538784505, 19431, 4582808236863555, 19939, 635, 19431,
    11049, 19939, 311277, 381, 561318416159695, 19431,
    635, 381, 635, 9779, 11049, 30120624602771,
    1034662650687541, 2913558341, 11443697140237983, 72095071289, 2293652311, 11443702633378745,
    1177821457, 1177821457, 39859957729, 2169671105, 72095071289, 39859957729,
    1034657020566299, 2293652311, 2169671105, 2913558341, 413604875733281, 872458245,
    284696901, 11631402765222347, 2874520323, 3308837957874989, 5758224417, 2580639651,
    872458245, 284696901, 308459935, 11178690145
  ]
def negativeCoefficients : Array ℕ := #[
    11705310468901200343578181632, 171625301163702668334624407552, 11724009047925004177992843264, 10508601411377754941039837184, 14210920058090914155142840320, 579655949737918866854510592,
    563554395578532231664107520, 20423397832931430241235107840, 20423405338450425231808921600, 563546890059537241090293760, 65277190574847542858788896768, 221272046577832755222112370688,
    65277190574847542858788896768, 8333084005155610096838901760, 75042374074460528426614784, 8332630031901974712268357632, 75779529026076054246129664, 8478202108575379356202827776,
    315994093608900006153321185280, 187925100807454875949725646848, 1289945841740571629276186542080, 192838175338368728915731546112, 6141343163642316207507374080, 187925100807454875949725646848,
    106859371047376302010628308992, 192838175338368728915731546112, 3010486418817463404920114774016, 117913788741932471184141582336, 315994176231624925293408419840, 187925100807454875949725646848,
    6141343163642316207507374080, 117913788741932471184141582336, 6141343163642316207507374080, 189153369440183339191227121664, 106859371047376302010628308992, 8478202108575379356202827776,
    582463291011322414322042273792, 214982660240995131688667316224, 12884457544129147736425488187392, 5319677316176113577742980612096, 169241668700357869627248738304, 12884463728855819945646101626880,
    173815767854421595833390596096, 173815767854421595833390596096, 2941145756062975950549214560256, 160093470392230417214965022720, 5319677316176113577742980612096, 2941145756062975950549214560256,
    582460121534831474082775564288, 169241668700357869627248738304, 160093470392230417214965022720, 214982660240995131688667316224, 3725421528462049230251729354752, 515008446736409153364232765440,
    21006923485300899676698968064, 13095795289812879680042096918528, 424204325864463328955275935744, 3725420348528788350267488731136, 424881968557537551525492031488, 380835193507713084461445808128,
    515008446736409153364232765440, 21006923485300899676698968064, 11380162955876167000701009920, 412420872368228236484296048640
  ]
def negativeScales : Array ℕ := #[
    26, 48, 27, 26, 24, 22,
    24, 30, 33, 27, 33, 34,
    33, 43, 23, 43, 22, 44,
    49, 14, 52, 14, 9, 14,
    13, 14, 18, 8, 48, 14,
    9, 8, 9, 13, 13, 44,
    49, 31, 53, 36, 31, 53,
    30, 30, 35, 31, 36, 35,
    49, 31, 31, 31, 48, 29,
    28, 53, 31, 51, 32, 31,
    29, 28, 28, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26241149857507427, 48115177003712580, 27243452643376847, 26085557330795734, 24520986618906294, 22905327325765521,
    24864685338750894, 30044209563655511, 33044210093840210, 27864666124549588, 33720565624337153, 34481735957907484,
    33720565624337153, 43750909086052935, 23955907854025280, 43750830488164636, 22970010560187291, 44775816921001215,
    49995812366454313, 14246072529464818, 52025153342120176, 14283305435663794, 9310612781659529, 14246072529464818,
    13431628182620918, 14283305435663794, 18247839455639006, 8573647187496003, 48995812743674725, 14246072529464818,
    9310612781659529, 8573647187496003, 9310612781659529, 13255471227467068, 13431628182620918, 44775816921001215,
    49878081883326219, 31440135053440598, 53345402740260376, 36069181583236147, 31094999567391878, 53345403432774774,
    30133473715206514, 30133473715206514, 35214221129090876, 31014829218707895, 36069181583236147, 35214221129090876,
    49878074032873196, 31094999567391878, 31014829218707895, 31440135053440598, 48555246521221492, 29700510846170192,
    28084851548152857, 53368874616762195, 31420674084698615, 51555246064284171, 32422976870568037, 31265081557986908,
    29700510846170192, 28084851548152857, 28200507873010081, 33380032100201257
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
noncomputable def negativeCeiling : ℝ := 5151309061 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 11705310468901200343578181632, coefficient := (-11705310468901200343578181632) }, { argument := 171625301163702668334624407552, coefficient := (-171625301163702668334624407552) }, { argument := 11724009047925004177992843264, coefficient := (-11724009047925004177992843264) }, { argument := 10508601411377754941039837184, coefficient := (-10508601411377754941039837184) }, { argument := 14210920058090914155142840320, coefficient := (-14210920058090914155142840320) }, { argument := 579655949737918866854510592, coefficient := (-579655949737918866854510592) }, { argument := 563554395578532231664107520, coefficient := (-563554395578532231664107520) }, { argument := 20423397832931430241235107840, coefficient := (-20423397832931430241235107840) }, { argument := 20423405338450425231808921600, coefficient := (-20423405338450425231808921600) }, { argument := 563546890059537241090293760, coefficient := (-563546890059537241090293760) }, { argument := 65277190574847542858788896768, coefficient := (-65277190574847542858788896768) }, { argument := 221272046577832755222112370688, coefficient := (-221272046577832755222112370688) }, { argument := 65277190574847542858788896768, coefficient := (-65277190574847542858788896768) }, { argument := 8333084005155610096838901760, coefficient := (-8333084005155610096838901760) }, { argument := 75042374074460528426614784, coefficient := (-75042374074460528426614784) }, { argument := 8332630031901974712268357632, coefficient := (-8332630031901974712268357632) }, { argument := 75779529026076054246129664, coefficient := (-75779529026076054246129664) }, { argument := 8478202108575379356202827776, coefficient := (-8478202108575379356202827776) }, { argument := 315994093608900006153321185280, coefficient := (-315994093608900006153321185280) }, { argument := 187925100807454875949725646848, coefficient := (-187925100807454875949725646848) }, { argument := 1289945841740571629276186542080, coefficient := (-1289945841740571629276186542080) }, { argument := 192838175338368728915731546112, coefficient := (-192838175338368728915731546112) }, { argument := 6141343163642316207507374080, coefficient := (-6141343163642316207507374080) }, { argument := 187925100807454875949725646848, coefficient := (-187925100807454875949725646848) }, { argument := 106859371047376302010628308992, coefficient := (-106859371047376302010628308992) }, { argument := 192838175338368728915731546112, coefficient := (-192838175338368728915731546112) }, { argument := 3010486418817463404920114774016, coefficient := (-3010486418817463404920114774016) }, { argument := 117913788741932471184141582336, coefficient := (-117913788741932471184141582336) }, { argument := 315994176231624925293408419840, coefficient := (-315994176231624925293408419840) }, { argument := 187925100807454875949725646848, coefficient := (-187925100807454875949725646848) }, { argument := 6141343163642316207507374080, coefficient := (-6141343163642316207507374080) }, { argument := 117913788741932471184141582336, coefficient := (-117913788741932471184141582336) }, { argument := 6141343163642316207507374080, coefficient := (-6141343163642316207507374080) }, { argument := 189153369440183339191227121664, coefficient := (-189153369440183339191227121664) }, { argument := 106859371047376302010628308992, coefficient := (-106859371047376302010628308992) }, { argument := 8478202108575379356202827776, coefficient := (-8478202108575379356202827776) }, { argument := 582463291011322414322042273792, coefficient := (-582463291011322414322042273792) }, { argument := 214982660240995131688667316224, coefficient := (-214982660240995131688667316224) }, { argument := 12884457544129147736425488187392, coefficient := (-12884457544129147736425488187392) }, { argument := 5319677316176113577742980612096, coefficient := (-5319677316176113577742980612096) }, { argument := 169241668700357869627248738304, coefficient := (-169241668700357869627248738304) }, { argument := 12884463728855819945646101626880, coefficient := (-12884463728855819945646101626880) }, { argument := 173815767854421595833390596096, coefficient := (-173815767854421595833390596096) }, { argument := 173815767854421595833390596096, coefficient := (-173815767854421595833390596096) }, { argument := 2941145756062975950549214560256, coefficient := (-2941145756062975950549214560256) }, { argument := 160093470392230417214965022720, coefficient := (-160093470392230417214965022720) }, { argument := 5319677316176113577742980612096, coefficient := (-5319677316176113577742980612096) }, { argument := 2941145756062975950549214560256, coefficient := (-2941145756062975950549214560256) }, { argument := 582460121534831474082775564288, coefficient := (-582460121534831474082775564288) }, { argument := 169241668700357869627248738304, coefficient := (-169241668700357869627248738304) }, { argument := 160093470392230417214965022720, coefficient := (-160093470392230417214965022720) }, { argument := 214982660240995131688667316224, coefficient := (-214982660240995131688667316224) }, { argument := 3725421528462049230251729354752, coefficient := (-3725421528462049230251729354752) }, { argument := 515008446736409153364232765440, coefficient := (-515008446736409153364232765440) }, { argument := 21006923485300899676698968064, coefficient := (-21006923485300899676698968064) }, { argument := 13095795289812879680042096918528, coefficient := (-13095795289812879680042096918528) }, { argument := 424204325864463328955275935744, coefficient := (-424204325864463328955275935744) }, { argument := 3725420348528788350267488731136, coefficient := (-3725420348528788350267488731136) }, { argument := 424881968557537551525492031488, coefficient := (-424881968557537551525492031488) }, { argument := 380835193507713084461445808128, coefficient := (-380835193507713084461445808128) }, { argument := 515008446736409153364232765440, coefficient := (-515008446736409153364232765440) }, { argument := 21006923485300899676698968064, coefficient := (-21006923485300899676698968064) }, { argument := 11380162955876167000701009920, coefficient := (-11380162955876167000701009920) }, { argument := 412420872368228236484296048640, coefficient := (-412420872368228236484296048640) }] }

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

end TermShard1


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5
