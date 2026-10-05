import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2826327823815191041796160406683648)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    89429554025, 2467646615, 350254384443, 593633884869, 350254384443, 550408121766045,
    1201660943, 550323570241379, 606732539, 11143088757, 18886030731, 11143088757,
    19125, 19125, 627671, 298587312396499, 1719050427, 3256523717100665,
    42537354183, 1353295017, 3256525290322159, 694935279, 694935279, 23518072863,
    1280143935, 42537354183, 23518072863, 298585732508765, 1353295017, 1280143935,
    1719050427, 413605075505799, 6979668525, 2277576045, 11631408346959213, 22996171035,
    3308839556054619, 46065812265, 20645124795, 6979668525, 2277576045, 2232890014943375,
    12524711045, 2231978634016625, 6323871785, 5722126659, 9698231997, 5722126659,
    19625, 19625, 17021993, 625, 625, 105,
    8216033, 606732539, 6323871785, 606732539, 8216033, 617905365,
    22393094955, 179144825475, 4943177085, 5722126659
  ]
def negativeCoefficients : Array ℕ := #[
    412421023931289232100399513600, 11380011392815171384597544960, 1615263247628674305207903977472, 5475306173830202006879078449152, 1615263247628674305207903977472, 309852226510906856343380951040,
    11083365939446740651494866944, 309804628234034430730722869248, 11192239868124999400527233024, 51388426622752320973940195328, 174192887731485360494003355648, 51388426622752320973940195328,
    184965650401038263730044928000, 184965650401038263730044928000, 2964092492669273080925782016, 168089713605803847174940786688, 63421766553340248358926680064, 3666519749714434356635720744960,
    1569351372373078911519824019456, 49927773669650833814474194944, 3666521521004367894049472905216, 51277172958019775268919443456, 51277172958019775268919443456, 867663742421229355208294793216,
    47228975092912950905583697920, 1569351372373078911519824019456, 867663742421229355208294793216, 168088824208077580972777799680, 49927773669650833814474194944, 47228975092912950905583697920,
    63421766553340248358926680064, 3725423327852924477583139012608, 515008636000003349624232345600, 21006931205263294524146319360, 13095801574289897129482137894912, 424204481757897495874696642560,
    3725422147919084885046781280256, 424882124700002763439991685120, 380835333463160371695813918720, 515008636000003349624232345600, 21006931205263294524146319360, 1257005329907285611887198208000,
    115520069622139157623456399360, 1256492268057022627223437312000, 116654844372847793749423554560, 52777303017961843162425065472, 178900803616120099966814257152, 52777303017961843162425065472,
    189801353679496780428869632000, 189801353679496780428869632000, 80384089214841720740016816128, 6044629098073145873530880000, 6044629098073145873530880000, 2030995376952577013506375680,
    75779529026076054246129664, 11192239868124999400527233024, 116654844372847793749423554560, 11192239868124999400527233024, 75779529026076054246129664, 11398342129927087395270819840,
    413079691653161508427561697280, 413079843458336020011103027200, 11398190324752575811729489920, 52777303017961843162425065472
  ]
def negativeScales : Array ℕ := #[
    36, 31, 38, 39, 38, 48,
    30, 48, 29, 33, 34, 33,
    14, 14, 19, 48, 30, 51,
    35, 30, 51, 29, 29, 34,
    30, 35, 34, 48, 30, 30,
    30, 48, 32, 31, 53, 34,
    51, 35, 34, 32, 31, 50,
    33, 50, 32, 32, 33, 32,
    14, 14, 24, 9, 9, 6,
    22, 29, 32, 29, 22, 29,
    34, 37, 32, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36380032630385956, 31200488658809597, 38349612154016174, 39110782487702920, 38349612154016174, 48967495100845715,
    30162382741004284, 48967273462648872, 29176485444122467, 33375430138171907, 34136600471858651, 33375430138171907,
    14223172127354739, 14223172127354739, 19259649028709589, 48085146192048437, 30678964719797598, 51532254157100086,
    35308011249549401, 30333829233705132, 51532254854063627, 29372303381519770, 29372303381519770, 34453050795404182,
    30253658885021149, 35308011249549401, 34453050795404182, 48085138558427937, 30333829233705132, 30253658885021149,
    30678964719797598, 48555247218047783, 32700511376354892, 31084852078337556, 53368875309089881, 34420674614883315,
    51555246761110459, 35422977400752737, 34265082088171607, 32700511376354892, 31084852078337556, 50987833633129705,
    33544058268562338, 50987244659398502, 32558160971681111, 32413904285986552, 33175074619673287, 32413904285986552,
    14260405033553715, 14260405033553715, 24020896627374360, 9287712379549450, 9287712379549450, 6714245517766967,
    22970010560187291, 29176485444122467, 32558160971681111, 29176485444122467, 22970010560187291, 29202810658879501,
    34382334886070678, 37382335416255377, 32202791444679018, 32413904285986552
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
noncomputable def negativeCeiling : ℝ := 27868946301 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 412421023931289232100399513600, coefficient := (-412421023931289232100399513600) }, { argument := 11380011392815171384597544960, coefficient := (-11380011392815171384597544960) }, { argument := 1615263247628674305207903977472, coefficient := (-1615263247628674305207903977472) }, { argument := 5475306173830202006879078449152, coefficient := (-5475306173830202006879078449152) }, { argument := 1615263247628674305207903977472, coefficient := (-1615263247628674305207903977472) }, { argument := 309852226510906856343380951040, coefficient := (-309852226510906856343380951040) }, { argument := 11083365939446740651494866944, coefficient := (-11083365939446740651494866944) }, { argument := 309804628234034430730722869248, coefficient := (-309804628234034430730722869248) }, { argument := 11192239868124999400527233024, coefficient := (-11192239868124999400527233024) }, { argument := 51388426622752320973940195328, coefficient := (-51388426622752320973940195328) }, { argument := 174192887731485360494003355648, coefficient := (-174192887731485360494003355648) }, { argument := 51388426622752320973940195328, coefficient := (-51388426622752320973940195328) }, { argument := 184965650401038263730044928000, coefficient := (-184965650401038263730044928000) }, { argument := 184965650401038263730044928000, coefficient := (-184965650401038263730044928000) }, { argument := 2964092492669273080925782016, coefficient := (-2964092492669273080925782016) }, { argument := 168089713605803847174940786688, coefficient := (-168089713605803847174940786688) }, { argument := 63421766553340248358926680064, coefficient := (-63421766553340248358926680064) }, { argument := 3666519749714434356635720744960, coefficient := (-3666519749714434356635720744960) }, { argument := 1569351372373078911519824019456, coefficient := (-1569351372373078911519824019456) }, { argument := 49927773669650833814474194944, coefficient := (-49927773669650833814474194944) }, { argument := 3666521521004367894049472905216, coefficient := (-3666521521004367894049472905216) }, { argument := 51277172958019775268919443456, coefficient := (-51277172958019775268919443456) }, { argument := 51277172958019775268919443456, coefficient := (-51277172958019775268919443456) }, { argument := 867663742421229355208294793216, coefficient := (-867663742421229355208294793216) }, { argument := 47228975092912950905583697920, coefficient := (-47228975092912950905583697920) }, { argument := 1569351372373078911519824019456, coefficient := (-1569351372373078911519824019456) }, { argument := 867663742421229355208294793216, coefficient := (-867663742421229355208294793216) }, { argument := 168088824208077580972777799680, coefficient := (-168088824208077580972777799680) }, { argument := 49927773669650833814474194944, coefficient := (-49927773669650833814474194944) }, { argument := 47228975092912950905583697920, coefficient := (-47228975092912950905583697920) }, { argument := 63421766553340248358926680064, coefficient := (-63421766553340248358926680064) }, { argument := 3725423327852924477583139012608, coefficient := (-3725423327852924477583139012608) }, { argument := 515008636000003349624232345600, coefficient := (-515008636000003349624232345600) }, { argument := 21006931205263294524146319360, coefficient := (-21006931205263294524146319360) }, { argument := 13095801574289897129482137894912, coefficient := (-13095801574289897129482137894912) }, { argument := 424204481757897495874696642560, coefficient := (-424204481757897495874696642560) }, { argument := 3725422147919084885046781280256, coefficient := (-3725422147919084885046781280256) }, { argument := 424882124700002763439991685120, coefficient := (-424882124700002763439991685120) }, { argument := 380835333463160371695813918720, coefficient := (-380835333463160371695813918720) }, { argument := 515008636000003349624232345600, coefficient := (-515008636000003349624232345600) }, { argument := 21006931205263294524146319360, coefficient := (-21006931205263294524146319360) }, { argument := 1257005329907285611887198208000, coefficient := (-1257005329907285611887198208000) }, { argument := 115520069622139157623456399360, coefficient := (-115520069622139157623456399360) }, { argument := 1256492268057022627223437312000, coefficient := (-1256492268057022627223437312000) }, { argument := 116654844372847793749423554560, coefficient := (-116654844372847793749423554560) }, { argument := 52777303017961843162425065472, coefficient := (-52777303017961843162425065472) }, { argument := 178900803616120099966814257152, coefficient := (-178900803616120099966814257152) }, { argument := 52777303017961843162425065472, coefficient := (-52777303017961843162425065472) }, { argument := 189801353679496780428869632000, coefficient := (-189801353679496780428869632000) }, { argument := 189801353679496780428869632000, coefficient := (-189801353679496780428869632000) }, { argument := 80384089214841720740016816128, coefficient := (-80384089214841720740016816128) }, { argument := 6044629098073145873530880000, coefficient := (-6044629098073145873530880000) }, { argument := 6044629098073145873530880000, coefficient := (-6044629098073145873530880000) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 75779529026076054246129664, coefficient := (-75779529026076054246129664) }, { argument := 11192239868124999400527233024, coefficient := (-11192239868124999400527233024) }, { argument := 116654844372847793749423554560, coefficient := (-116654844372847793749423554560) }, { argument := 11192239868124999400527233024, coefficient := (-11192239868124999400527233024) }, { argument := 75779529026076054246129664, coefficient := (-75779529026076054246129664) }, { argument := 11398342129927087395270819840, coefficient := (-11398342129927087395270819840) }, { argument := 413079691653161508427561697280, coefficient := (-413079691653161508427561697280) }, { argument := 413079843458336020011103027200, coefficient := (-413079843458336020011103027200) }, { argument := 11398190324752575811729489920, coefficient := (-11398190324752575811729489920) }, { argument := 52777303017961843162425065472, coefficient := (-52777303017961843162425065472) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2046947580520373685867065903153152)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    9698231997, 5722126659, 276924095, 10035820865, 80286596425, 2215363255,
    193648812723, 328208588109, 193648812723, 19125, 19125, 10540759635,
    17865164205, 10540759635, 10875, 10875, 93, 93622025,
    3392893175, 27143155375, 748966225, 350254384443, 593633884869, 350254384443,
    19625, 19625, 193648812723, 328208588109, 193648812723, 306375,
    306375, 4353, 375, 375, 1185, 38108279048613,
    192591315, 62845587, 1056521449962231, 634537701, 304866172499937, 1271102679,
    569664837, 192591315, 62845587, 275204132202315, 1201660943, 275161856407733,
    606732539, 8510997, 19125, 19125, 4353, 105,
    30550345, 1107154615, 8857240175, 244399505, 11143088757, 18886030731,
    11143088757, 625, 625, 10540759635
  ]
def negativeCoefficients : Array ℕ := #[
    178900803616120099966814257152, 52777303017961843162425065472, 10216695816617261748233175040, 370256438132498832115294535680, 370256574200294805815374643200, 10216559748821288048153067520,
    893047522119722767195771502592, 3027189913820137481017409667072, 893047522119722767195771502592, 184965650401038263730044928000, 184965650401038263730044928000, 48610673832333276596970455040,
    164777055962215881548381552640, 48610673832333276596970455040, 105176546306472738199437312000, 105176546306472738199437312000, 1798881619586568211962789888, 13816172278699499873055539200,
    500702656549286676881892966400, 500702840555558812134670336000, 13815988272427364620278169600, 1615263247628674305207903977472, 5475306173830202006879078449152, 1615263247628674305207903977472,
    189801353679496780428869632000, 189801353679496780428869632000, 893047522119722767195771502592, 3027189913820137481017409667072, 893047522119722767195771502592, 2963077183875456107204837376000,
    2963077183875456107204837376000, 84199265484519692759935746048, 116056878683004400771792896000, 116056878683004400771792896000, 22921233539893369152429096960, 171624431323064386621745922048,
    14210730794496717895143260160, 579648229775524019407159296, 594768701044854958351630467072, 11705154575467033424157474816, 171624397608573203521254457344, 11723852905459792263493189632,
    10508461455930467706671726592, 14210730794496717895143260160, 579648229775524019407159296, 309852306809291638175233474560, 11083365939446740651494866944, 309804708496110066466807611392,
    11192239868124999400527233024, 80384093937208203609662029824, 184965650401038263730044928000, 184965650401038263730044928000, 84199265484519692759935746048, 2030995376952577013506375680,
    563554395578532231664107520, 20423397832931430241235107840, 20423405338450425231808921600, 563546890059537241090293760, 51388426622752320973940195328, 174192887731485360494003355648,
    51388426622752320973940195328, 6044629098073145873530880000, 6044629098073145873530880000, 48610673832333276596970455040
  ]
def negativeScales : Array ℕ := #[
    33, 32, 28, 33, 36, 31,
    37, 38, 37, 14, 14, 33,
    34, 33, 13, 13, 6, 26,
    31, 34, 29, 38, 39, 38,
    14, 14, 37, 38, 37, 18,
    18, 12, 8, 8, 10, 45,
    27, 25, 49, 29, 48, 30,
    29, 27, 25, 47, 30, 47,
    29, 23, 14, 14, 12, 6,
    24, 30, 33, 27, 33, 34,
    33, 9, 9, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33175074619673287, 32413904285986552, 28044915346298388, 33224439573489562, 36224440103674261, 31044896132097905,
    37494651699871129, 38255822033557649, 37494651699871129, 14223172127354739, 14223172127354739, 33295259789487922,
    34056430123174668, 33295259789487922, 13408727780510825, 13408727780510825, 6539158811108986, 26480344634408549,
    31659868861626916, 34659869391811616, 29480325420208065, 38349612154016174, 39110782487702920, 38349612154016174,
    14260405033553715, 14260405033553715, 37494651699871129, 38255822033557649, 37494651699871129, 18224939053528927,
    18224939053528927, 12087794304787901, 8550746785384604, 8550746785384604, 10210671343785622, 45115169691748978,
    27520967404705811, 25905308111563394, 49908243486168094, 29241130643306943, 48115169408340994, 30243433429176364,
    29085538116595251, 27520967404705811, 25905308111563394, 47967495474721012, 30162382741004284, 47967273836412527,
    29176485444122467, 23020896712129124, 14223172127354739, 14223172127354739, 12087794304787901, 6714245517766967,
    24864685338750894, 30044209563655511, 33044210093840210, 27864666124549588, 33375430138171907, 34136600471858651,
    33375430138171907, 9287712379549450, 9287712379549450, 33295259789487922
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
noncomputable def negativeCeiling : ℝ := 12080130671 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 178900803616120099966814257152, coefficient := (-178900803616120099966814257152) }, { argument := 52777303017961843162425065472, coefficient := (-52777303017961843162425065472) }, { argument := 10216695816617261748233175040, coefficient := (-10216695816617261748233175040) }, { argument := 370256438132498832115294535680, coefficient := (-370256438132498832115294535680) }, { argument := 370256574200294805815374643200, coefficient := (-370256574200294805815374643200) }, { argument := 10216559748821288048153067520, coefficient := (-10216559748821288048153067520) }, { argument := 893047522119722767195771502592, coefficient := (-893047522119722767195771502592) }, { argument := 3027189913820137481017409667072, coefficient := (-3027189913820137481017409667072) }, { argument := 893047522119722767195771502592, coefficient := (-893047522119722767195771502592) }, { argument := 184965650401038263730044928000, coefficient := (-184965650401038263730044928000) }, { argument := 184965650401038263730044928000, coefficient := (-184965650401038263730044928000) }, { argument := 48610673832333276596970455040, coefficient := (-48610673832333276596970455040) }, { argument := 164777055962215881548381552640, coefficient := (-164777055962215881548381552640) }, { argument := 48610673832333276596970455040, coefficient := (-48610673832333276596970455040) }, { argument := 105176546306472738199437312000, coefficient := (-105176546306472738199437312000) }, { argument := 105176546306472738199437312000, coefficient := (-105176546306472738199437312000) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 13816172278699499873055539200, coefficient := (-13816172278699499873055539200) }, { argument := 500702656549286676881892966400, coefficient := (-500702656549286676881892966400) }, { argument := 500702840555558812134670336000, coefficient := (-500702840555558812134670336000) }, { argument := 13815988272427364620278169600, coefficient := (-13815988272427364620278169600) }, { argument := 1615263247628674305207903977472, coefficient := (-1615263247628674305207903977472) }, { argument := 5475306173830202006879078449152, coefficient := (-5475306173830202006879078449152) }, { argument := 1615263247628674305207903977472, coefficient := (-1615263247628674305207903977472) }, { argument := 189801353679496780428869632000, coefficient := (-189801353679496780428869632000) }, { argument := 189801353679496780428869632000, coefficient := (-189801353679496780428869632000) }, { argument := 893047522119722767195771502592, coefficient := (-893047522119722767195771502592) }, { argument := 3027189913820137481017409667072, coefficient := (-3027189913820137481017409667072) }, { argument := 893047522119722767195771502592, coefficient := (-893047522119722767195771502592) }, { argument := 2963077183875456107204837376000, coefficient := (-2963077183875456107204837376000) }, { argument := 2963077183875456107204837376000, coefficient := (-2963077183875456107204837376000) }, { argument := 84199265484519692759935746048, coefficient := (-84199265484519692759935746048) }, { argument := 116056878683004400771792896000, coefficient := (-116056878683004400771792896000) }, { argument := 116056878683004400771792896000, coefficient := (-116056878683004400771792896000) }, { argument := 22921233539893369152429096960, coefficient := (-22921233539893369152429096960) }, { argument := 171624431323064386621745922048, coefficient := (-171624431323064386621745922048) }, { argument := 14210730794496717895143260160, coefficient := (-14210730794496717895143260160) }, { argument := 579648229775524019407159296, coefficient := (-579648229775524019407159296) }, { argument := 594768701044854958351630467072, coefficient := (-594768701044854958351630467072) }, { argument := 11705154575467033424157474816, coefficient := (-11705154575467033424157474816) }, { argument := 171624397608573203521254457344, coefficient := (-171624397608573203521254457344) }, { argument := 11723852905459792263493189632, coefficient := (-11723852905459792263493189632) }, { argument := 10508461455930467706671726592, coefficient := (-10508461455930467706671726592) }, { argument := 14210730794496717895143260160, coefficient := (-14210730794496717895143260160) }, { argument := 579648229775524019407159296, coefficient := (-579648229775524019407159296) }, { argument := 309852306809291638175233474560, coefficient := (-309852306809291638175233474560) }, { argument := 11083365939446740651494866944, coefficient := (-11083365939446740651494866944) }, { argument := 309804708496110066466807611392, coefficient := (-309804708496110066466807611392) }, { argument := 11192239868124999400527233024, coefficient := (-11192239868124999400527233024) }, { argument := 80384093937208203609662029824, coefficient := (-80384093937208203609662029824) }, { argument := 184965650401038263730044928000, coefficient := (-184965650401038263730044928000) }, { argument := 184965650401038263730044928000, coefficient := (-184965650401038263730044928000) }, { argument := 84199265484519692759935746048, coefficient := (-84199265484519692759935746048) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 563554395578532231664107520, coefficient := (-563554395578532231664107520) }, { argument := 20423397832931430241235107840, coefficient := (-20423397832931430241235107840) }, { argument := 20423405338450425231808921600, coefficient := (-20423405338450425231808921600) }, { argument := 563546890059537241090293760, coefficient := (-563546890059537241090293760) }, { argument := 51388426622752320973940195328, coefficient := (-51388426622752320973940195328) }, { argument := 174192887731485360494003355648, coefficient := (-174192887731485360494003355648) }, { argument := 51388426622752320973940195328, coefficient := (-51388426622752320973940195328) }, { argument := 6044629098073145873530880000, coefficient := (-6044629098073145873530880000) }, { argument := 6044629098073145873530880000, coefficient := (-6044629098073145873530880000) }, { argument := 48610673832333276596970455040, coefficient := (-48610673832333276596970455040) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5
