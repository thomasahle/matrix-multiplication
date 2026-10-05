import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 22, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-359089085592184791104912625762304)
def positiveArguments : Array ℕ := #[
    227, 105, 1869, 105, 3325, 5677,
    105, 5677, 5677, 1869, 105, 483,
    541, 483, 541, 5, 237, 851443751,
    851443673, 701263549, 2506564327, 175315863
  ]
def positiveCoefficients : Array ℕ := #[
    35969585781476009267468953452544, 8123981507810308054025502720, 144606870839023483361653948416, 8123981507810308054025502720, 128629707206996544188737126400, 219618300094471994393822756864,
    8123981507810308054025502720, 219618300094471994393822756864, 219618300094471994393822756864, 144606870839023483361653948416, 8123981507810308054025502720, 149481259743709668194069250048,
    167431390313347682180106551296, 149481259743709668194069250048, 167431390313347682180106551296, 792281625142643375935439503360, 18777074515880648009669916229632, 16083317727084831859154075254784,
    16083316253706489203824768581632, 3311623479455815106927320367104, 11836915364981509283796685422592, 3311623021386266268571734638592
  ]
def positiveScales : Array ℕ := #[
    7, 6, 10, 6, 11, 12,
    6, 12, 12, 10, 6, 8,
    9, 8, 9, 2, 7, 29,
    29, 29, 31, 27
  ]
def negativeArguments : Array ℕ := #[
    87496977, 1869, 105, 157690101, 5677, 87496965,
    5677, 5677, 1869, 105, 425246759, 541,
    425246719, 541, 352995961, 541, 541, 1869,
    105, 425246721, 541, 425246681, 541, 1272281919,
    5677, 44124489, 541, 541, 5677, 5677,
    1869, 105, 7, 1, 5, 237,
    203, 233
  ]
def negativeCoefficients : Array ℕ := #[
    1652771166148864965043675987968, 72303435419511741680826974208, 4061990753905154027012751360, 5957363581141832988655110586368, 109809150047235997196911378432, 1652770939475273787300705730560,
    109809150047235997196911378432, 109809150047235997196911378432, 72303435419511741680826974208, 4061990753905154027012751360, 4016342083301091293208172822528, 41857847578336920545026637824,
    4016341705511772663636555726848, 41857847578336920545026637824, 1666976294814760449937669881856, 41857847578336920545026637824, 41857847578336920545026637824, 72303435419511741680826974208,
    4061990753905154027012751360, 4016341724401238595115136581632, 41857847578336920545026637824, 4016341346611919965543519485952, 41857847578336920545026637824, 6008181491046672839330311962624,
    109809150047235997196911378432, 1666976063418802789325054410752, 41857847578336920545026637824, 41857847578336920545026637824, 109809150047235997196911378432, 109809150047235997196911378432,
    72303435419511741680826974208, 4061990753905154027012751360, 1109194275199700726309615304704, 633825300114114700748351602688, 792281625142643375935439503360, 18777074515880648009669916229632,
    32166633980791321062978843836416, 18460161865823590659295740428288
  ]
def negativeScales : Array ℕ := #[
    26, 10, 6, 27, 12, 26,
    12, 12, 10, 6, 28, 9,
    28, 9, 28, 9, 9, 10,
    6, 28, 9, 28, 9, 30,
    12, 25, 9, 9, 12, 12,
    10, 6, 2, 0, 2, 7,
    7, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7826548487222833, 6714245517659862, 10868050853594526, 6714245517659862, 11699138625271509, 12470913026274870,
    6714245517659862, 12470913026274870, 12470913026274870, 10868050853594526, 6714245517659862, 8915879378478017,
    9079484783826815, 8915879378478017, 9079484783826815, 2321928094887362, 7888743248677875, 29665335983265231,
    29665335851101224, 29385381499167957, 31223064113062850, 27385381299611843
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    26382729837242814, 10868050856180197, 6714245517766967, 27232516856852859, 12470913026274977, 26382729639380645,
    12470913026274977, 12470913026274977, 10868050856180197, 6714245517766967, 28663724999620957, 9079484783826816,
    28663724863916679, 9079484783826816, 28395076435290525, 9079484783826816, 9079484783826816, 10868050856180197,
    6714245517766967, 28663724870701894, 9079484783826816, 28663724734997604, 9079484783826816, 30244771240078628,
    12470913026274977, 25395076235027435, 9079484783826816, 9079484783826816, 12470913026274977, 12470913026274977,
    10868050856180197, 6714245517766967, 2807354922807594, 0, 2321928094887363, 7888743252462684,
    7665335917216502, 7864186146919547
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 38
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
noncomputable def positiveFloor : ℝ := 4723573447 / 200000000000
noncomputable def negativeCeiling : ℝ := 2318115327 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1652771166148864965043675987968, coefficient := (-1652771166148864965043675987968) }, { argument := 72303435419511741680826974208, coefficient := (-72303435419511741680826974208) }, { argument := 4061990753905154027012751360, coefficient := (-4061990753905154027012751360) }, { argument := 5957363581141832988655110586368, coefficient := (-5957363581141832988655110586368) }, { argument := 109809150047235997196911378432, coefficient := (-109809150047235997196911378432) }, { argument := 1652770939475273787300705730560, coefficient := (-1652770939475273787300705730560) }, { argument := 109809150047235997196911378432, coefficient := (-109809150047235997196911378432) }, { argument := 109809150047235997196911378432, coefficient := (-109809150047235997196911378432) }, { argument := 72303435419511741680826974208, coefficient := (-72303435419511741680826974208) }, { argument := 4061990753905154027012751360, coefficient := (-4061990753905154027012751360) }, { argument := 4016342083301091293208172822528, coefficient := (-4016342083301091293208172822528) }, { argument := 41857847578336920545026637824, coefficient := (-41857847578336920545026637824) }, { argument := 4016341705511772663636555726848, coefficient := (-4016341705511772663636555726848) }, { argument := 41857847578336920545026637824, coefficient := (-41857847578336920545026637824) }, { argument := 1666976294814760449937669881856, coefficient := (-1666976294814760449937669881856) }, { argument := 41857847578336920545026637824, coefficient := (-41857847578336920545026637824) }, { argument := 41857847578336920545026637824, coefficient := (-41857847578336920545026637824) }, { argument := 72303435419511741680826974208, coefficient := (-72303435419511741680826974208) }, { argument := 4061990753905154027012751360, coefficient := (-4061990753905154027012751360) }, { argument := 4016341724401238595115136581632, coefficient := (-4016341724401238595115136581632) }, { argument := 41857847578336920545026637824, coefficient := (-41857847578336920545026637824) }, { argument := 4016341346611919965543519485952, coefficient := (-4016341346611919965543519485952) }, { argument := 41857847578336920545026637824, coefficient := (-41857847578336920545026637824) }, { argument := 6008181491046672839330311962624, coefficient := (-6008181491046672839330311962624) }, { argument := 109809150047235997196911378432, coefficient := (-109809150047235997196911378432) }, { argument := 1666976063418802789325054410752, coefficient := (-1666976063418802789325054410752) }, { argument := 41857847578336920545026637824, coefficient := (-41857847578336920545026637824) }, { argument := 41857847578336920545026637824, coefficient := (-41857847578336920545026637824) }, { argument := 109809150047235997196911378432, coefficient := (-109809150047235997196911378432) }, { argument := 109809150047235997196911378432, coefficient := (-109809150047235997196911378432) }, { argument := 72303435419511741680826974208, coefficient := (-72303435419511741680826974208) }, { argument := 4061990753905154027012751360, coefficient := (-4061990753905154027012751360) }, { argument := 35969585781476009267468953452544, coefficient := 35969585781476009267468953452544 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 128629707206996544188737126400, coefficient := 128629707206996544188737126400 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 18777074515880648009669916229632, coefficient := 18777074515880648009669916229632 }, { argument := 18777074515880648009669916229632, coefficient := (-18777074515880648009669916229632) }, { argument := 16083317727084831859154075254784, coefficient := 16083317727084831859154075254784 }, { argument := 16083316253706489203824768581632, coefficient := 16083316253706489203824768581632 }, { argument := 32166633980791321062978843836416, coefficient := (-32166633980791321062978843836416) }, { argument := 3311623479455815106927320367104, coefficient := 3311623479455815106927320367104 }, { argument := 11836915364981509283796685422592, coefficient := 11836915364981509283796685422592 }, { argument := 3311623021386266268571734638592, coefficient := 3311623021386266268571734638592 }, { argument := 18460161865823590659295740428288, coefficient := (-18460161865823590659295740428288) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22
