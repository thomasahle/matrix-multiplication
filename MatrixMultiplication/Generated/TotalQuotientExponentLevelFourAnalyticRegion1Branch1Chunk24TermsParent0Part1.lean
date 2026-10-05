import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 24, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24

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
def constantNumerator : ℤ := 271037612186567393724635616903168
def positiveArguments : Array ℕ := #[
    5, 3, 45, 79, 3, 25,
    3, 79, 157, 25, 2423, 155,
    45, 79, 3, 155, 3, 79,
    79, 3, 9, 41
  ]
def positiveCoefficients : Array ℕ := #[
    3169126500570573503741758013440, 232113757366008801543585792, 3481706360490132023153786880, 6112328943971565107314425856, 232113757366008801543585792, 3868562622766813359059763200,
    232113757366008801543585792, 6112328943971565107314425856, 6073643317743896973723828224, 3868562622766813359059763200, 93735272349639887690018062336, 5996272065288560706542632960,
    3481706360490132023153786880, 6112328943971565107314425856, 232113757366008801543585792, 5996272065288560706542632960, 232113757366008801543585792, 6112328943971565107314425856,
    6112328943971565107314425856, 232113757366008801543585792, 5570730176784211237046059008, 6344442701337573908858011648
  ]
def positiveScales : Array ℕ := #[
    2, 1, 5, 6, 1, 4,
    1, 6, 7, 4, 11, 7,
    5, 6, 1, 7, 1, 6,
    6, 1, 3, 5
  ]
def negativeArguments : Array ℕ := #[
    37, 507080651, 59267883675, 16226575365, 699, 699,
    79, 37, 37, 157, 362942489, 42420930825,
    11614155735, 429, 429, 25, 699, 699,
    2423, 155, 17431539, 8780685, 17431539, 8780685,
    4742751, 79, 18828859, 2200728075, 602523285, 37,
    37, 3, 37, 37, 155, 3,
    41, 41, 79, 79, 3849, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1431368170423720942852112384, 18707973987454062836718764032, 68331217621444583182093516800, 18707967684432197151086346240, 54082505466280050759655489536, 54082505466280050759655489536,
    3056164471985782553657212928, 1431368170423720942852112384, 1431368170423720942852112384, 3036821658871948486861914112, 13390214416116288253170024448, 48908003393581974390256435200,
    13390209904734440726577807360, 16596133651669629310366384128, 16596133651669629310366384128, 1934281311383406679529881600, 54082505466280050759655489536, 54082505466280050759655489536,
    46867636174819943845009031168, 2998136032644280353271316480, 2572441109951095389334536192, 1295800391894882833850695680, 2572441109951095389334536192, 1295800391894882833850695680,
    22397008358996492706901917696, 3056164471985782553657212928, 694662286345925508661772288, 2537266723459529977312051200, 694662052302860073471836160, 1431368170423720942852112384,
    1431368170423720942852112384, 116056878683004400771792896, 1431368170423720942852112384, 1431368170423720942852112384, 2998136032644280353271316480, 116056878683004400771792896,
    1586110675334393477214502912, 1586110675334393477214502912, 3056164471985782553657212928, 3056164471985782553657212928, 290822217481044230840254464, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    5, 28, 35, 33, 9, 9,
    6, 5, 5, 7, 28, 35,
    33, 8, 8, 4, 9, 9,
    11, 7, 24, 23, 24, 23,
    22, 6, 24, 31, 29, 5,
    5, 1, 5, 5, 7, 1,
    5, 5, 6, 6, 11, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 1584962500720924, 5491853096329661, 6303780748177102, 1584962500720924, 4643856189773592,
    1584962500720924, 6303780748177102, 7294620748891626, 4643856189773592, 11242578689451346, 7276124405274237,
    5491853096329661, 6303780748177102, 1584962500720924, 7276124405274237, 1584962500720924, 6303780748177102,
    6303780748177102, 1584962500720924, 3169925001442312, 5357552004618083
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5209453365628950, 28917639990690431, 35786531492340501, 33917639504622786, 9449148645375482, 9449148645375482,
    6303780748177104, 5209453365628950, 5209453365628950, 7294620748891628, 28435165719419595, 35304057226552041,
    33435165233352000, 8744833837700333, 8744833837700333, 4643856189792934, 9449148645375482, 9449148645375482,
    11242578689451347, 7276124405274238, 24055196612312628, 23065902061198067, 24055196612312628, 23065902061198067,
    22177292696545105, 6303780748177104, 24166442241703951, 31035333748836422, 29166441755636356, 5209453365628950,
    5209453365628950, 1584962500724866, 5209453365628950, 5209453365628950, 7276124405274238, 1584962500724866,
    5357552004618085, 5357552004618085, 6303780748177104, 6303780748177104, 11910267961055196, 0
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 13337903 / 125000000000
noncomputable def negativeCeiling : ℝ := 30267677 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 18707973987454062836718764032, coefficient := (-18707973987454062836718764032) }, { argument := 68331217621444583182093516800, coefficient := (-68331217621444583182093516800) }, { argument := 18707967684432197151086346240, coefficient := (-18707967684432197151086346240) }, { argument := 54082505466280050759655489536, coefficient := (-54082505466280050759655489536) }, { argument := 54082505466280050759655489536, coefficient := (-54082505466280050759655489536) }, { argument := 3056164471985782553657212928, coefficient := (-3056164471985782553657212928) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 3036821658871948486861914112, coefficient := (-3036821658871948486861914112) }, { argument := 13390214416116288253170024448, coefficient := (-13390214416116288253170024448) }, { argument := 48908003393581974390256435200, coefficient := (-48908003393581974390256435200) }, { argument := 13390209904734440726577807360, coefficient := (-13390209904734440726577807360) }, { argument := 16596133651669629310366384128, coefficient := (-16596133651669629310366384128) }, { argument := 16596133651669629310366384128, coefficient := (-16596133651669629310366384128) }, { argument := 1934281311383406679529881600, coefficient := (-1934281311383406679529881600) }, { argument := 54082505466280050759655489536, coefficient := (-54082505466280050759655489536) }, { argument := 54082505466280050759655489536, coefficient := (-54082505466280050759655489536) }, { argument := 46867636174819943845009031168, coefficient := (-46867636174819943845009031168) }, { argument := 2998136032644280353271316480, coefficient := (-2998136032644280353271316480) }, { argument := 2572441109951095389334536192, coefficient := (-2572441109951095389334536192) }, { argument := 1295800391894882833850695680, coefficient := (-1295800391894882833850695680) }, { argument := 2572441109951095389334536192, coefficient := (-2572441109951095389334536192) }, { argument := 1295800391894882833850695680, coefficient := (-1295800391894882833850695680) }, { argument := 22397008358996492706901917696, coefficient := (-22397008358996492706901917696) }, { argument := 3056164471985782553657212928, coefficient := (-3056164471985782553657212928) }, { argument := 694662286345925508661772288, coefficient := (-694662286345925508661772288) }, { argument := 2537266723459529977312051200, coefficient := (-2537266723459529977312051200) }, { argument := 694662052302860073471836160, coefficient := (-694662052302860073471836160) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 116056878683004400771792896, coefficient := (-116056878683004400771792896) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 2998136032644280353271316480, coefficient := (-2998136032644280353271316480) }, { argument := 116056878683004400771792896, coefficient := (-116056878683004400771792896) }, { argument := 1586110675334393477214502912, coefficient := (-1586110675334393477214502912) }, { argument := 1586110675334393477214502912, coefficient := (-1586110675334393477214502912) }, { argument := 3056164471985782553657212928, coefficient := (-3056164471985782553657212928) }, { argument := 3056164471985782553657212928, coefficient := (-3056164471985782553657212928) }, { argument := 290822217481044230840254464, coefficient := (-290822217481044230840254464) }, { argument := 3169126500570573503741758013440, coefficient := 3169126500570573503741758013440 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3868562622766813359059763200, coefficient := 3868562622766813359059763200 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 3868562622766813359059763200, coefficient := 3868562622766813359059763200 }, { argument := 93735272349639887690018062336, coefficient := 93735272349639887690018062336 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 6344442701337573908858011648, coefficient := 6344442701337573908858011648 }] }

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
def constantNumerator : ℤ := (-82922246748110076213657016991744)
def positiveArguments : Array ℕ := #[
    1, 429, 19, 1, 19, 37,
    699, 37, 429, 699, 9, 37,
    37, 41, 49, 245, 203, 3647,
    1365, 49, 5467, 5467, 3913, 203,
    305, 335, 305, 335, 3, 1,
    1, 1, 649271, 75887175, 20776665, 1048435,
    20447305, 40894595, 131055, 2313, 1093527, 41509413,
    4374111, 2313
  ]
def positiveCoefficients : Array ℕ := #[
    4951760157141521099596496896, 66384534606678517241465536512, 5880215186605556305770840064, 4951760157141521099596496896, 5880215186605556305770840064, 5725472681694883771408449536,
    216330021865120203038621958144, 5725472681694883771408449536, 66384534606678517241465536512, 216330021865120203038621958144, 5570730176784211237046059008, 5725472681694883771408449536,
    5725472681694883771408449536, 6344442701337573908858011648, 7582382740622954183757135872, 151647654812459083675142717440, 7853182124216631118891319296, 141086478852305683204909563904,
    211223519203068009404663070720, 7582382740622954183757135872, 211494318586661686339797254144, 211494318586661686339797254144, 151376855428865406740008534016, 7853182124216631118891319296,
    188785855991020491922116444160, 207354956580301196045603307520, 188785855991020491922116444160, 207354956580301196045603307520, 475368975085586025561263702016, 158456325028528675187087900672,
    316912650057057350374175801344, 316912650057057350374175801344, 196230118956752474722663399424, 716734103399326537039321497600, 196230052843621714547630407680, 9902188606934872959242731520,
    386238671188051643704929157120, 386238529517057157615572746240, 9902235830599701655694868480, 349530677596079660136923136, 41312282023303956172778766336, 392045321349587056677561040896,
    41312310357502853390650048512, 349530677596079660136923136
  ]
def positiveScales : Array ℕ := #[
    0, 8, 4, 0, 4, 5,
    9, 5, 8, 9, 3, 5,
    5, 5, 5, 7, 7, 11,
    10, 5, 12, 12, 11, 7,
    8, 8, 8, 8, 1, 0,
    0, 0, 19, 26, 24, 19,
    24, 25, 16, 11, 20, 25,
    22, 11
  ]
def negativeArguments : Array ℕ := #[
    1, 7, 5, 3, 1, 1,
    7, 5, 3
  ]
def negativeCoefficients : Array ℕ := #[
    633825300114114700748351602688, 1109194275199700726309615304704, 792281625142643375935439503360, 475368975085586025561263702016, 158456325028528675187087900672, 633825300114114700748351602688,
    1109194275199700726309615304704, 792281625142643375935439503360, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    0, 2, 2, 1, 0, 0,
    2, 2, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 8744833837487090, 4247927513443585, 0, 4247927513443585, 5209453365628949,
    9449148645375433, 5209453365628949, 8744833837487090, 9449148645375433, 3169925001442312, 5209453365628949,
    5209453365628949, 5357552004618083, 5614709844114682, 7936637938489789, 7665335917183229, 11832494484259625,
    10414685235807213, 5614709844114682, 12416533660199582, 12416533660199582, 11934059394410200, 7665335917183229,
    8252665432450248, 8388017285345134, 8252665432450248, 8388017285345134, 1584962500720924, 0,
    0, 0, 19308461246576377, 26177352753708849, 24308460760508782, 19999805989070412,
    24285407369512956, 25285406840337361, 16999812869285053, 11175549550636190, 20060557411370183, 25306935194611816,
    22060558400848184, 11175549550636190
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 2807354922807594, 2321928094887363, 1584962500724866, 0, 0,
    2807354922807594, 2321928094887363, 1584962500724866
  ]

abbrev PositiveTerm := Fin 44
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 1006999717 / 1000000000000
noncomputable def negativeCeiling : ℝ := 27478037 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4951760157141521099596496896, coefficient := 4951760157141521099596496896 }, { argument := 66384534606678517241465536512, coefficient := 66384534606678517241465536512 }, { argument := 5880215186605556305770840064, coefficient := 5880215186605556305770840064 }, { argument := 4951760157141521099596496896, coefficient := 4951760157141521099596496896 }, { argument := 5880215186605556305770840064, coefficient := 5880215186605556305770840064 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 216330021865120203038621958144, coefficient := 216330021865120203038621958144 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 66384534606678517241465536512, coefficient := 66384534606678517241465536512 }, { argument := 216330021865120203038621958144, coefficient := 216330021865120203038621958144 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 6344442701337573908858011648, coefficient := 6344442701337573908858011648 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 151647654812459083675142717440, coefficient := 151647654812459083675142717440 }, { argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 141086478852305683204909563904, coefficient := 141086478852305683204909563904 }, { argument := 211223519203068009404663070720, coefficient := 211223519203068009404663070720 }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 151376855428865406740008534016, coefficient := 151376855428865406740008534016 }, { argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 196230118956752474722663399424, coefficient := 196230118956752474722663399424 }, { argument := 716734103399326537039321497600, coefficient := 716734103399326537039321497600 }, { argument := 196230052843621714547630407680, coefficient := 196230052843621714547630407680 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 9902188606934872959242731520, coefficient := 9902188606934872959242731520 }, { argument := 386238671188051643704929157120, coefficient := 386238671188051643704929157120 }, { argument := 386238529517057157615572746240, coefficient := 386238529517057157615572746240 }, { argument := 9902235830599701655694868480, coefficient := 9902235830599701655694868480 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 349530677596079660136923136, coefficient := 349530677596079660136923136 }, { argument := 41312282023303956172778766336, coefficient := 41312282023303956172778766336 }, { argument := 392045321349587056677561040896, coefficient := 392045321349587056677561040896 }, { argument := 41312310357502853390650048512, coefficient := 41312310357502853390650048512 }, { argument := 349530677596079660136923136, coefficient := 349530677596079660136923136 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24
