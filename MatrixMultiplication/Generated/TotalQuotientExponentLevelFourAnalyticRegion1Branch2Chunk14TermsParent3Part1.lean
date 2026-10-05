import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 14, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-16254366045984556034943975233159168)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    13365675, 13365675, 28216425, 13779133119879, 47478568809, 83423628695673,
    20603907219, 3967211949, 82287654297, 41335789017, 13779133119879, 47478568809,
    3967211949, 169512944171061, 5220619666687947, 183836565, 1728063711, 20405858715,
    1433925207, 2610309215996865, 20405858715, 183836565, 1433925207, 1433925207,
    1433925207, 1433925207, 1433925207, 84757089432639, 1728063711, 17909319095743,
    1564615297757515, 322123756955, 56418844784088961, 10619464515, 24778750535, 322123756955,
    322123756955, 10619464515, 3975219550115, 159291967725, 1564615297757515, 322123756955,
    24778750535, 159291967725, 24778750535, 322123756955, 322123756955, 78882795982635,
    13365675, 1119096405, 559548405, 6682635, 13742103, 1014818349,
    10577281935, 1014818349, 13742103, 9415486698309, 2362536855, 329444727572795,
    37178869455, 1119096405, 2635554007996957, 1119096405
  ]
def negativeCoefficients : Array ℕ := #[
    246553186097377911295180800, 246553186097377911295180800, 260250585325010017478246400, 15513924696043881097378922496, 109478125975703989285099143168, 187853311553863770025601531904,
    95018750846837424662538878976, 4573883969335341870401716224, 94871206202665316860267855872, 95313840135181640267080925184, 15513924696043881097378922496, 109478125975703989285099143168,
    4573883969335341870401716224, 381709216101633005778924208128, 11755790392769460569312493305856, 217035908220471729713640898560, 255017192159054282413528055808, 3011373226559045249776767467520,
    6771520336478717967065596035072, 11755787612485252770459329495040, 3011373226559045249776767467520, 217035908220471729713640898560, 211610010514959936470799876096, 211610010514959936470799876096,
    211610010514959936470799876096, 6771520336478717967065596035072, 211610010514959936470799876096, 381711996385840804632088018944, 255017192159054282413528055808, 161312805612094966351114797056,
    14092801743917844399609746554880, 2971067252305351105007205744640, 127043944173148448305771685347328, 1567156352864361022421383249920, 114271817396359657884892528640, 2971067252305351105007205744640,
    2971067252305351105007205744640, 1567156352864361022421383249920, 36664928838889113087066945617920, 2938418161620676917040093593600, 14092801743917844399609746554880, 2971067252305351105007205744640,
    114271817396359657884892528640, 2938418161620676917040093593600, 114271817396359657884892528640, 2971067252305351105007205744640, 2971067252305351105007205744640, 177628265296668922428763668480,
    246553186097377911295180800, 20643684976843414227627540480, 20643692447774764079995944960, 246545715166028058926776320, 1013988228302225001563553792, 149760754922459691811835215872,
    1560931302803330789958934855680, 149760754922459691811835215872, 1013988228302225001563553792, 339228659088130192724157530112, 21790556364445826129162403840, 11869497218688113049074202050560,
    171457272446560579279462072320, 20643684976843414227627540480, 11869480048329912780081879580672, 20643684976843414227627540480
  ]
def negativeScales : Array ℕ := #[
    23, 23, 24, 43, 35, 46,
    34, 31, 36, 35, 43, 35,
    31, 47, 52, 27, 30, 34,
    30, 51, 34, 27, 30, 30,
    30, 30, 30, 46, 30, 44,
    50, 38, 55, 33, 34, 38,
    38, 33, 41, 37, 50, 38,
    34, 37, 34, 38, 38, 46,
    23, 30, 29, 22, 23, 29,
    33, 29, 23, 43, 31, 48,
    35, 30, 51, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23672029363375464, 23672029363375464, 24750031875564819, 43647550360858355, 35466557396000156, 46245521300346817,
    34262198897493885, 31885478333124769, 36259956946707215, 35266672374073193, 43647550360858355, 35466557396000156,
    31885478333124769, 47268388771568639, 52213142482404270, 27453848505582455, 30686509262425207, 34248264371932508,
    30417322629557301, 51213142141201971, 34248264371932508, 27453848505582455, 30417322629557301, 30417322629557301,
    30417322629557301, 30417322629557301, 30417322629557301, 46268399279797054, 30686509262425207, 44025775721285679,
    50474729399162632, 38228824108633410, 55647026644238009, 33305991969155870, 34528384390492999, 38228824108633410,
    38228824108633410, 33305991969155870, 41854171682710607, 37212882564764389, 50474729399162632, 38228824108633410,
    34528384390492999, 37212882564764389, 34528384390492999, 38228824108633410, 38228824108633410, 46164775922153075,
    23672029363375464, 30059687177185791, 29059687699295757, 22671985646889411, 23712099465807666, 29918574370275067,
    33300249891761266, 29918574370275067, 23712099465807666, 43098172810130316, 31137689689187065, 48227029766507607,
    35113763849941584, 30059687177185791, 51227027679510316, 30059687177185791
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
noncomputable def negativeCeiling : ℝ := 34365997717 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 260250585325010017478246400, coefficient := (-260250585325010017478246400) }, { argument := 15513924696043881097378922496, coefficient := (-15513924696043881097378922496) }, { argument := 109478125975703989285099143168, coefficient := (-109478125975703989285099143168) }, { argument := 187853311553863770025601531904, coefficient := (-187853311553863770025601531904) }, { argument := 95018750846837424662538878976, coefficient := (-95018750846837424662538878976) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 94871206202665316860267855872, coefficient := (-94871206202665316860267855872) }, { argument := 95313840135181640267080925184, coefficient := (-95313840135181640267080925184) }, { argument := 15513924696043881097378922496, coefficient := (-15513924696043881097378922496) }, { argument := 109478125975703989285099143168, coefficient := (-109478125975703989285099143168) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 381709216101633005778924208128, coefficient := (-381709216101633005778924208128) }, { argument := 11755790392769460569312493305856, coefficient := (-11755790392769460569312493305856) }, { argument := 217035908220471729713640898560, coefficient := (-217035908220471729713640898560) }, { argument := 255017192159054282413528055808, coefficient := (-255017192159054282413528055808) }, { argument := 3011373226559045249776767467520, coefficient := (-3011373226559045249776767467520) }, { argument := 6771520336478717967065596035072, coefficient := (-6771520336478717967065596035072) }, { argument := 11755787612485252770459329495040, coefficient := (-11755787612485252770459329495040) }, { argument := 3011373226559045249776767467520, coefficient := (-3011373226559045249776767467520) }, { argument := 217035908220471729713640898560, coefficient := (-217035908220471729713640898560) }, { argument := 211610010514959936470799876096, coefficient := (-211610010514959936470799876096) }, { argument := 211610010514959936470799876096, coefficient := (-211610010514959936470799876096) }, { argument := 211610010514959936470799876096, coefficient := (-211610010514959936470799876096) }, { argument := 6771520336478717967065596035072, coefficient := (-6771520336478717967065596035072) }, { argument := 211610010514959936470799876096, coefficient := (-211610010514959936470799876096) }, { argument := 381711996385840804632088018944, coefficient := (-381711996385840804632088018944) }, { argument := 255017192159054282413528055808, coefficient := (-255017192159054282413528055808) }, { argument := 161312805612094966351114797056, coefficient := (-161312805612094966351114797056) }, { argument := 14092801743917844399609746554880, coefficient := (-14092801743917844399609746554880) }, { argument := 2971067252305351105007205744640, coefficient := (-2971067252305351105007205744640) }, { argument := 127043944173148448305771685347328, coefficient := (-127043944173148448305771685347328) }, { argument := 1567156352864361022421383249920, coefficient := (-1567156352864361022421383249920) }, { argument := 114271817396359657884892528640, coefficient := (-114271817396359657884892528640) }, { argument := 2971067252305351105007205744640, coefficient := (-2971067252305351105007205744640) }, { argument := 2971067252305351105007205744640, coefficient := (-2971067252305351105007205744640) }, { argument := 1567156352864361022421383249920, coefficient := (-1567156352864361022421383249920) }, { argument := 36664928838889113087066945617920, coefficient := (-36664928838889113087066945617920) }, { argument := 2938418161620676917040093593600, coefficient := (-2938418161620676917040093593600) }, { argument := 14092801743917844399609746554880, coefficient := (-14092801743917844399609746554880) }, { argument := 2971067252305351105007205744640, coefficient := (-2971067252305351105007205744640) }, { argument := 114271817396359657884892528640, coefficient := (-114271817396359657884892528640) }, { argument := 2938418161620676917040093593600, coefficient := (-2938418161620676917040093593600) }, { argument := 114271817396359657884892528640, coefficient := (-114271817396359657884892528640) }, { argument := 2971067252305351105007205744640, coefficient := (-2971067252305351105007205744640) }, { argument := 2971067252305351105007205744640, coefficient := (-2971067252305351105007205744640) }, { argument := 177628265296668922428763668480, coefficient := (-177628265296668922428763668480) }, { argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 1013988228302225001563553792, coefficient := (-1013988228302225001563553792) }, { argument := 149760754922459691811835215872, coefficient := (-149760754922459691811835215872) }, { argument := 1560931302803330789958934855680, coefficient := (-1560931302803330789958934855680) }, { argument := 149760754922459691811835215872, coefficient := (-149760754922459691811835215872) }, { argument := 1013988228302225001563553792, coefficient := (-1013988228302225001563553792) }, { argument := 339228659088130192724157530112, coefficient := (-339228659088130192724157530112) }, { argument := 21790556364445826129162403840, coefficient := (-21790556364445826129162403840) }, { argument := 11869497218688113049074202050560, coefficient := (-11869497218688113049074202050560) }, { argument := 171457272446560579279462072320, coefficient := (-171457272446560579279462072320) }, { argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }, { argument := 11869480048329912780081879580672, coefficient := (-11869480048329912780081879580672) }, { argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3788329907693689460382544903012352)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1119096405, 95869258695, 1119096405, 37178869455, 95869258695, 75327706171875,
    1119096405, 1119096405, 2362536855, 32064907, 2367909481, 24680324515,
    2367909481, 32064907, 78019515, 2931393605, 5862343795, 156482445,
    54738645397119, 196772731145061, 13684658119047, 13365675, 1119096405, 559548405,
    6682635, 1144992825, 95869258695, 47934646695, 572479065, 416843791,
    30782823253, 320844218695, 30782823253, 416843791, 13365675, 1119096405,
    559548405, 6682635, 416843791, 30782823253, 320844218695, 30782823253,
    416843791, 733383441, 27555099887, 55106031673, 1470934983, 444037425,
    37178869455, 18589441455, 222011985, 13742103, 1014818349, 10577281935,
    1014818349, 13742103, 1144992825, 95869258695, 47934646695, 572479065,
    5144127223, 379880335309, 3959429204335, 379880335309
  ]
def negativeCoefficients : Array ℕ := #[
    20643684976843414227627540480, 884237839841459576083379650560, 20643684976843414227627540480, 171457272446560579279462072320, 884237839841459576083379650560, 339245829446330461716480000000,
    20643684976843414227627540480, 20643684976843414227627540480, 21790556364445826129162403840, 73936641647037239697342464, 10920055046429352527946317824, 113817907496076203434505666560,
    10920055046429352527946317824, 73936641647037239697342464, 5756824103839773871791144960, 216298670442975312938239262720, 216282311316928425096579645440, 5773183229886661713450762240,
    15407558938326927777479000064, 55386599916348219518160470016, 15407555301408175472485859328, 246553186097377911295180800, 20643684976843414227627540480, 20643692447774764079995944960,
    246545715166028058926776320, 10560694804504353867143577600, 884237839841459576083379650560, 884238159846352394759826309120, 10560374799611535190696919040, 1922352682822968232130904064,
    283921431207163165726604263424, 2959265594897981289297147330560, 283921431207163165726604263424, 1922352682822968232130904064, 246553186097377911295180800, 20643684976843414227627540480,
    20643692447774764079995944960, 246545715166028058926776320, 1922352682822968232130904064, 283921431207163165726604263424, 2959265594897981289297147330560, 283921431207163165726604263424,
    1922352682822968232130904064, 6764268322011734299354595328, 254150937770495992702431133696, 254131715797390899488481083392, 6783490295116827513304645632, 2047761184530999874368307200,
    171457272446560579279462072320, 171457334496795957219966320640, 2047699134295621933864058880, 1013988228302225001563553792, 149760754922459691811835215872, 1560931302803330789958934855680,
    149760754922459691811835215872, 1013988228302225001563553792, 10560694804504353867143577600, 884237839841459576083379650560, 884238159846352394759826309120, 10560374799611535190696919040,
    23723099591320805765747310592, 3503777662040046539681061404672, 36519288605169593273414246727680, 3503777662040046539681061404672
  ]
def negativeScales : Array ℕ := #[
    30, 36, 30, 35, 36, 46,
    30, 30, 31, 24, 31, 34,
    31, 24, 26, 31, 32, 27,
    45, 47, 43, 23, 30, 29,
    22, 30, 36, 35, 29, 28,
    34, 38, 34, 28, 23, 30,
    29, 22, 28, 34, 38, 34,
    28, 29, 34, 35, 30, 28,
    35, 34, 27, 23, 29, 33,
    29, 23, 30, 36, 35, 29,
    32, 38, 41, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30059687177185791, 36480349225658652, 30059687177185791, 35113763849941584, 36480349225658652, 46098245831566051,
    30059687177185791, 30059687177185791, 31137689689187065, 24934491895051345, 31140966785540769, 34522642313098282,
    31140966785540769, 24934491895051345, 26217331694241922, 31448939549020401, 32448830430815822, 27221425576435589,
    45637624966700563, 47483523633614673, 43637624626155686, 23672029363375464, 30059687177185791, 29059687699295757,
    22671985646889411, 30092691411811231, 36480349225658652, 35480349747768618, 29092647695325218, 28634931605203684,
    34841406505150601, 38223082031238806, 34841406505150601, 28634931605203684, 23672029363375464, 30059687177185791,
    29059687699295757, 22671985646889411, 28634931605203684, 34841406505150601, 38223082031238806, 34841406505150601,
    28634931605203684, 29449992451032244, 34681600305857299, 35681491187652596, 30454086333225918, 28726106036226496,
    35113763849941584, 34113764372051550, 27726062319740353, 23712099465807666, 29918574370275067, 33300249891761266,
    29918574370275067, 23712099465807666, 30092691411811231, 36480349225658652, 35480349747768618, 29092647695325218,
    32260279177391137, 38466754075883852, 41848429605121633, 38466754075883852
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
noncomputable def negativeCeiling : ℝ := 28876065447 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }, { argument := 884237839841459576083379650560, coefficient := (-884237839841459576083379650560) }, { argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }, { argument := 171457272446560579279462072320, coefficient := (-171457272446560579279462072320) }, { argument := 884237839841459576083379650560, coefficient := (-884237839841459576083379650560) }, { argument := 339245829446330461716480000000, coefficient := (-339245829446330461716480000000) }, { argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }, { argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }, { argument := 21790556364445826129162403840, coefficient := (-21790556364445826129162403840) }, { argument := 73936641647037239697342464, coefficient := (-73936641647037239697342464) }, { argument := 10920055046429352527946317824, coefficient := (-10920055046429352527946317824) }, { argument := 113817907496076203434505666560, coefficient := (-113817907496076203434505666560) }, { argument := 10920055046429352527946317824, coefficient := (-10920055046429352527946317824) }, { argument := 73936641647037239697342464, coefficient := (-73936641647037239697342464) }, { argument := 5756824103839773871791144960, coefficient := (-5756824103839773871791144960) }, { argument := 216298670442975312938239262720, coefficient := (-216298670442975312938239262720) }, { argument := 216282311316928425096579645440, coefficient := (-216282311316928425096579645440) }, { argument := 5773183229886661713450762240, coefficient := (-5773183229886661713450762240) }, { argument := 15407558938326927777479000064, coefficient := (-15407558938326927777479000064) }, { argument := 55386599916348219518160470016, coefficient := (-55386599916348219518160470016) }, { argument := 15407555301408175472485859328, coefficient := (-15407555301408175472485859328) }, { argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 10560694804504353867143577600, coefficient := (-10560694804504353867143577600) }, { argument := 884237839841459576083379650560, coefficient := (-884237839841459576083379650560) }, { argument := 884238159846352394759826309120, coefficient := (-884238159846352394759826309120) }, { argument := 10560374799611535190696919040, coefficient := (-10560374799611535190696919040) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }, { argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 2959265594897981289297147330560, coefficient := (-2959265594897981289297147330560) }, { argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }, { argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }, { argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 2959265594897981289297147330560, coefficient := (-2959265594897981289297147330560) }, { argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }, { argument := 6764268322011734299354595328, coefficient := (-6764268322011734299354595328) }, { argument := 254150937770495992702431133696, coefficient := (-254150937770495992702431133696) }, { argument := 254131715797390899488481083392, coefficient := (-254131715797390899488481083392) }, { argument := 6783490295116827513304645632, coefficient := (-6783490295116827513304645632) }, { argument := 2047761184530999874368307200, coefficient := (-2047761184530999874368307200) }, { argument := 171457272446560579279462072320, coefficient := (-171457272446560579279462072320) }, { argument := 171457334496795957219966320640, coefficient := (-171457334496795957219966320640) }, { argument := 2047699134295621933864058880, coefficient := (-2047699134295621933864058880) }, { argument := 1013988228302225001563553792, coefficient := (-1013988228302225001563553792) }, { argument := 149760754922459691811835215872, coefficient := (-149760754922459691811835215872) }, { argument := 1560931302803330789958934855680, coefficient := (-1560931302803330789958934855680) }, { argument := 149760754922459691811835215872, coefficient := (-149760754922459691811835215872) }, { argument := 1013988228302225001563553792, coefficient := (-1013988228302225001563553792) }, { argument := 10560694804504353867143577600, coefficient := (-10560694804504353867143577600) }, { argument := 884237839841459576083379650560, coefficient := (-884237839841459576083379650560) }, { argument := 884238159846352394759826309120, coefficient := (-884238159846352394759826309120) }, { argument := 10560374799611535190696919040, coefficient := (-10560374799611535190696919040) }, { argument := 23723099591320805765747310592, coefficient := (-23723099591320805765747310592) }, { argument := 3503777662040046539681061404672, coefficient := (-3503777662040046539681061404672) }, { argument := 36519288605169593273414246727680, coefficient := (-36519288605169593273414246727680) }, { argument := 3503777662040046539681061404672, coefficient := (-3503777662040046539681061404672) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14
