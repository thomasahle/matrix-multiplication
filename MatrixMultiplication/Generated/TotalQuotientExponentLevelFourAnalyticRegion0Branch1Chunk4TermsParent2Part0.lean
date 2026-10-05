import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 9469439102693981070606559346688
def positiveArguments : Array ℕ := #[
    5, 25154919, 25176729, 53143967, 178903051, 26582827,
    3895541, 138672745, 138710641, 3933745, 42451, 502137,
    42127631, 2008563, 84893
  ]
def positiveCoefficients : Array ℕ := #[
    3169126500570573503741758013440, 237581492729801625818521141248, 237787482355784399742742560768, 501930577055060981076736344064, 1689691543451037528035522772992, 502135404978888969068235194368,
    36792344502089001170813059072, 1309727046151058357918671831040, 1310084963751528014068708278272, 37153171080312105022301143040, 801876718257197235866435584, 37940399017739440618714693632,
    397884225274200469327002468352, 37940682359728412797427515392, 801791715660505582252589056
  ]
def positiveScales : Array ℕ := #[
    2, 24, 24, 25, 27, 24,
    21, 27, 27, 21, 15, 18,
    25, 20, 16
  ]
def negativeArguments : Array ℕ := #[
    355948678003, 2105198403393, 353239189821803, 16841713001079, 711821891249, 12181967271461,
    433504015638225, 433621460606091, 12300369940095, 12181967271461, 40987346137873, 6093509692261,
    355948678003, 356260918413, 356260918413, 2107032051903, 353545175033493, 16856382299529,
    712446306639, 40987346137873, 1459357709488745, 1459758593108123, 41391480951275, 433504015638225,
    1459357709488745, 216840435525475, 2105198403393, 2107032051903, 6093509692261, 216840435525475,
    216899165920621, 6152719331275, 433621460606091, 1459758593108123, 216899165920621, 353239189821803,
    353545175033493, 12300369940095, 41391480951275, 6152719331275, 16841713001079, 16856382299529,
    711821891249, 712446306639, 3, 17, 17, 3
  ]
def negativeCoefficients : Array ℕ := #[
    200381291702166433285799936, 9480970745061677922074492928, 99427992728382993383731232768, 9481041549492527787197595648, 200360050261447382971449344, 3428918954024458593203388416,
    122020532705745236294998425600, 122053590525340102387298205696, 3462246342420693262868152320, 3428918954024458593203388416, 11536912299589398823004274688, 3430340997430643169198866432,
    200381291702166433285799936, 200557067426432184647417856, 200557067426432184647417856, 9489228763808042387282853888, 99514119908717241279770001408, 9489299630371678611516162048,
    200535807568805408154845184, 11536912299589398823004274688, 410772677290860783539553566720, 410885515998288889573894258688, 11650666136779692081309286400, 122020532705745236294998425600,
    410772677290860783539553566720, 122070313078923159124783923200, 9480970745061677922074492928, 9489228763808042387282853888, 3430340997430643169198866432, 122070313078923159124783923200,
    122103375352135015073161674752, 3463673060955667166973132800, 122053590525340102387298205696, 410885515998288889573894258688, 122103375352135015073161674752, 99427992728382993383731232768,
    99514119908717241279770001408, 3462246342420693262868152320, 11650666136779692081309286400, 3463673060955667166973132800, 9481041549492527787197595648, 9489299630371678611516162048,
    200360050261447382971449344, 200535807568805408154845184, 475368975085586025561263702016, 2693757525484987478180494311424, 2693757525484987478180494311424, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    38, 40, 48, 43, 39, 43,
    48, 48, 43, 43, 45, 42,
    38, 38, 38, 40, 48, 43,
    39, 45, 50, 50, 45, 48,
    50, 47, 40, 40, 42, 47,
    47, 42, 48, 50, 47, 48,
    48, 43, 45, 42, 43, 43,
    39, 39, 1, 4, 4, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 24584337208297596, 24585587522247618, 25663402587890850, 27414602750317878, 24663991203060202,
    21893392268056393, 27047109024646762, 27047503225412698, 21907472008798165, 15373510918676367, 18937721507922041,
    25328263454057903, 20937732282045744, 16373357978302620
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38372878286839943, 40937093352804172, 48327638738864489, 43937104126894425, 39372725345688100, 43469812367075587,
    48623038685928086, 48623429488132481, 43483766939564983, 43469812367075587, 45220243814440861, 42470410558429742,
    38372878286839943, 38374143273220917, 38374143273220917, 40938349407614410, 48328887898854496, 43938360181774847,
    39373990333624584, 45220243814440861, 50374254975142508, 50374651227126557, 45234399101404172, 48623038685928086,
    50374254975142508, 47623627138135727, 40937093352804172, 40938349407614410, 42470410558429742, 47623627138135727,
    47624017833613318, 42484361321238923, 48623429488132481, 50374651227126557, 47624017833613318, 48327638738864489,
    48328887898854496, 43483766939564983, 45234399101404172, 42484361321238923, 43937104126894425, 43938360181774847,
    39372725345688100, 39373990333624584, 1584962500724866, 4087462841250340, 4087462841250340, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 131450671 / 62500000000
noncomputable def negativeCeiling : ℝ := 215578443 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 200381291702166433285799936, coefficient := (-200381291702166433285799936) }, { argument := 9480970745061677922074492928, coefficient := (-9480970745061677922074492928) }, { argument := 99427992728382993383731232768, coefficient := (-99427992728382993383731232768) }, { argument := 9481041549492527787197595648, coefficient := (-9481041549492527787197595648) }, { argument := 200360050261447382971449344, coefficient := (-200360050261447382971449344) }, { argument := 3428918954024458593203388416, coefficient := (-3428918954024458593203388416) }, { argument := 122020532705745236294998425600, coefficient := (-122020532705745236294998425600) }, { argument := 122053590525340102387298205696, coefficient := (-122053590525340102387298205696) }, { argument := 3462246342420693262868152320, coefficient := (-3462246342420693262868152320) }, { argument := 3428918954024458593203388416, coefficient := (-3428918954024458593203388416) }, { argument := 11536912299589398823004274688, coefficient := (-11536912299589398823004274688) }, { argument := 3430340997430643169198866432, coefficient := (-3430340997430643169198866432) }, { argument := 200381291702166433285799936, coefficient := (-200381291702166433285799936) }, { argument := 200557067426432184647417856, coefficient := (-200557067426432184647417856) }, { argument := 200557067426432184647417856, coefficient := (-200557067426432184647417856) }, { argument := 9489228763808042387282853888, coefficient := (-9489228763808042387282853888) }, { argument := 99514119908717241279770001408, coefficient := (-99514119908717241279770001408) }, { argument := 9489299630371678611516162048, coefficient := (-9489299630371678611516162048) }, { argument := 200535807568805408154845184, coefficient := (-200535807568805408154845184) }, { argument := 11536912299589398823004274688, coefficient := (-11536912299589398823004274688) }, { argument := 410772677290860783539553566720, coefficient := (-410772677290860783539553566720) }, { argument := 410885515998288889573894258688, coefficient := (-410885515998288889573894258688) }, { argument := 11650666136779692081309286400, coefficient := (-11650666136779692081309286400) }, { argument := 122020532705745236294998425600, coefficient := (-122020532705745236294998425600) }, { argument := 410772677290860783539553566720, coefficient := (-410772677290860783539553566720) }, { argument := 122070313078923159124783923200, coefficient := (-122070313078923159124783923200) }, { argument := 9480970745061677922074492928, coefficient := (-9480970745061677922074492928) }, { argument := 9489228763808042387282853888, coefficient := (-9489228763808042387282853888) }, { argument := 3430340997430643169198866432, coefficient := (-3430340997430643169198866432) }, { argument := 122070313078923159124783923200, coefficient := (-122070313078923159124783923200) }, { argument := 122103375352135015073161674752, coefficient := (-122103375352135015073161674752) }, { argument := 3463673060955667166973132800, coefficient := (-3463673060955667166973132800) }, { argument := 122053590525340102387298205696, coefficient := (-122053590525340102387298205696) }, { argument := 410885515998288889573894258688, coefficient := (-410885515998288889573894258688) }, { argument := 122103375352135015073161674752, coefficient := (-122103375352135015073161674752) }, { argument := 99427992728382993383731232768, coefficient := (-99427992728382993383731232768) }, { argument := 99514119908717241279770001408, coefficient := (-99514119908717241279770001408) }, { argument := 3462246342420693262868152320, coefficient := (-3462246342420693262868152320) }, { argument := 11650666136779692081309286400, coefficient := (-11650666136779692081309286400) }, { argument := 3463673060955667166973132800, coefficient := (-3463673060955667166973132800) }, { argument := 9481041549492527787197595648, coefficient := (-9481041549492527787197595648) }, { argument := 9489299630371678611516162048, coefficient := (-9489299630371678611516162048) }, { argument := 200360050261447382971449344, coefficient := (-200360050261447382971449344) }, { argument := 200535807568805408154845184, coefficient := (-200535807568805408154845184) }, { argument := 3169126500570573503741758013440, coefficient := 3169126500570573503741758013440 }, { argument := 237581492729801625818521141248, coefficient := 237581492729801625818521141248 }, { argument := 237787482355784399742742560768, coefficient := 237787482355784399742742560768 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 501930577055060981076736344064, coefficient := 501930577055060981076736344064 }, { argument := 1689691543451037528035522772992, coefficient := 1689691543451037528035522772992 }, { argument := 502135404978888969068235194368, coefficient := 502135404978888969068235194368 }, { argument := 2693757525484987478180494311424, coefficient := (-2693757525484987478180494311424) }, { argument := 36792344502089001170813059072, coefficient := 36792344502089001170813059072 }, { argument := 1309727046151058357918671831040, coefficient := 1309727046151058357918671831040 }, { argument := 1310084963751528014068708278272, coefficient := 1310084963751528014068708278272 }, { argument := 37153171080312105022301143040, coefficient := 37153171080312105022301143040 }, { argument := 2693757525484987478180494311424, coefficient := (-2693757525484987478180494311424) }, { argument := 801876718257197235866435584, coefficient := 801876718257197235866435584 }, { argument := 37940399017739440618714693632, coefficient := 37940399017739440618714693632 }, { argument := 397884225274200469327002468352, coefficient := 397884225274200469327002468352 }, { argument := 37940682359728412797427515392, coefficient := 37940682359728412797427515392 }, { argument := 801791715660505582252589056, coefficient := 801791715660505582252589056 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4
