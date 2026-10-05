import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 19, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2785549309344201774175187929923584)
def positiveArguments : Array ℕ := #[
    59385, 535, 4173, 4173, 4173, 4173,
    4173, 4815, 5029, 3915, 16443, 71253,
    2349, 2349, 5481, 71253, 71253, 2349,
    879309, 35235, 16443, 71253, 5481, 35235,
    5481, 71253, 71253, 2349, 1605, 30495,
    46545, 479895, 14445, 46545, 14445, 14445,
    1237455, 14445, 479895, 1237455, 1605, 14445,
    14445, 30495, 1395, 24831, 1395, 44175,
    75423, 1395, 75423, 75423, 24831, 1395,
    483, 541, 483, 541, 125
  ]
def positiveCoefficients : Array ℕ := #[
    1148672956765036056638820188160, 82787240127209805883878932480, 80717559124029560736781959168, 80717559124029560736781959168, 80717559124029560736781959168, 2582961891968945943577022693376,
    80717559124029560736781959168, 93135645143111031619363799040, 97275007149471521913557745664, 151454226681320743007189729280, 2544431008246188482520787451904, 5512933851200075045461706145792,
    181745072017584891608627675136, 2907921152281358265738042802176, 212035917353849040210065620992, 5512933851200075045461706145792, 5512933851200075045461706145792, 2907921152281358265738042802176,
    68033238625249277758829626392576, 5452352160527546748258830254080, 2544431008246188482520787451904, 5512933851200075045461706145792, 212035917353849040210065620992, 5452352160527546748258830254080,
    212035917353849040210065620992, 5512933851200075045461706145792, 5512933851200075045461706145792, 181745072017584891608627675136, 993446881526517670606547189760, 1179718171812739733845274787840,
    900311236383406638987183390720, 9282519299263399484729925304320, 1117627741717332379432365588480, 900311236383406638987183390720, 1117627741717332379432365588480, 1117627741717332379432365588480,
    47871721603559070252352992706560, 1117627741717332379432365588480, 9282519299263399484729925304320, 47871721603559070252352992706560, 993446881526517670606547189760, 1117627741717332379432365588480,
    1117627741717332379432365588480, 1179718171812739733845274787840, 53966448587597046358883696640, 960602784859227425188129800192, 53966448587597046358883696640, 854468769303619900682325196800,
    1458892993484706819901822599168, 53966448587597046358883696640, 1458892993484706819901822599168, 1458892993484706819901822599168, 960602784859227425188129800192, 53966448587597046358883696640,
    37370314935927417048517312512, 41857847578336920545026637824, 37370314935927417048517312512, 41857847578336920545026637824, 4951760157141521099596496896000
  ]
def positiveScales : Array ℕ := #[
    15, 9, 12, 12, 12, 12,
    12, 12, 12, 11, 14, 16,
    11, 11, 12, 16, 16, 11,
    19, 15, 14, 16, 12, 15,
    12, 16, 16, 11, 10, 14,
    15, 18, 13, 15, 13, 13,
    20, 13, 18, 20, 10, 13,
    13, 14, 10, 14, 10, 15,
    16, 10, 16, 16, 14, 10,
    8, 9, 8, 9, 6
  ]
def negativeArguments : Array ℕ := #[
    107, 783, 1605, 93, 1
  ]
def negativeCoefficients : Array ℕ := #[
    8477413389026284122509202685952, 124071302497337952671489826226176, 127161200835394261837638040289280, 7368219113826583396199587381248, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    6, 9, 10, 6, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15857810947514299, 9063395081288509, 12026869205263395, 12026869205263395, 12026869205263395, 12026869205263395,
    12026869205263395, 12233320082730821, 12296055838078784, 11934796591681559, 14005185920069800, 16120663137489736,
    11197830998012196, 11197830998012196, 12420223419348643, 16120663137489736, 16120663137489736, 11197830998012196,
    19746010709678859, 15104721593620715, 14005185920069800, 16120663137489736, 12420223419348643, 15104721593620715,
    12420223419348643, 16120663137489736, 16120663137489736, 11197830998012196, 10648357582008395, 14896285095200692,
    15506338577137216, 18872359256044585, 13818282583394157, 15506338577137216, 13818282583394157, 13818282583394157,
    20238944631924699, 13818282583394157, 18872359256044585, 20238944631924699, 10648357582008395, 13818282583394157,
    13818282583394157, 14896285095200692, 10446049406716546, 14599854742795234, 10446049406716546, 15430942514326339,
    16202716915325304, 10446049406716546, 16202716915325304, 16202716915325304, 14599854742795234, 10446049406716546,
    8915879378478017, 9079484783826815, 8915879378478017, 9079484783826815, 6965784283824454
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6741466986587556, 9612868497299083, 10648357582030099, 6539158811108986, 0
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
noncomputable def positiveFloor : ℝ := 58537148803 / 1000000000000
noncomputable def negativeCeiling : ℝ := 124699789 / 3906250000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1148672956765036056638820188160, coefficient := 1148672956765036056638820188160 }, { argument := 82787240127209805883878932480, coefficient := 82787240127209805883878932480 }, { argument := 80717559124029560736781959168, coefficient := 80717559124029560736781959168 }, { argument := 80717559124029560736781959168, coefficient := 80717559124029560736781959168 }, { argument := 80717559124029560736781959168, coefficient := 80717559124029560736781959168 }, { argument := 2582961891968945943577022693376, coefficient := 2582961891968945943577022693376 }, { argument := 80717559124029560736781959168, coefficient := 80717559124029560736781959168 }, { argument := 93135645143111031619363799040, coefficient := 93135645143111031619363799040 }, { argument := 97275007149471521913557745664, coefficient := 97275007149471521913557745664 }, { argument := 8477413389026284122509202685952, coefficient := (-8477413389026284122509202685952) }, { argument := 151454226681320743007189729280, coefficient := 151454226681320743007189729280 }, { argument := 2544431008246188482520787451904, coefficient := 2544431008246188482520787451904 }, { argument := 5512933851200075045461706145792, coefficient := 5512933851200075045461706145792 }, { argument := 181745072017584891608627675136, coefficient := 181745072017584891608627675136 }, { argument := 2907921152281358265738042802176, coefficient := 2907921152281358265738042802176 }, { argument := 212035917353849040210065620992, coefficient := 212035917353849040210065620992 }, { argument := 5512933851200075045461706145792, coefficient := 5512933851200075045461706145792 }, { argument := 5512933851200075045461706145792, coefficient := 5512933851200075045461706145792 }, { argument := 2907921152281358265738042802176, coefficient := 2907921152281358265738042802176 }, { argument := 68033238625249277758829626392576, coefficient := 68033238625249277758829626392576 }, { argument := 5452352160527546748258830254080, coefficient := 5452352160527546748258830254080 }, { argument := 2544431008246188482520787451904, coefficient := 2544431008246188482520787451904 }, { argument := 5512933851200075045461706145792, coefficient := 5512933851200075045461706145792 }, { argument := 212035917353849040210065620992, coefficient := 212035917353849040210065620992 }, { argument := 5452352160527546748258830254080, coefficient := 5452352160527546748258830254080 }, { argument := 212035917353849040210065620992, coefficient := 212035917353849040210065620992 }, { argument := 5512933851200075045461706145792, coefficient := 5512933851200075045461706145792 }, { argument := 5512933851200075045461706145792, coefficient := 5512933851200075045461706145792 }, { argument := 181745072017584891608627675136, coefficient := 181745072017584891608627675136 }, { argument := 124071302497337952671489826226176, coefficient := (-124071302497337952671489826226176) }, { argument := 993446881526517670606547189760, coefficient := 993446881526517670606547189760 }, { argument := 1179718171812739733845274787840, coefficient := 1179718171812739733845274787840 }, { argument := 900311236383406638987183390720, coefficient := 900311236383406638987183390720 }, { argument := 9282519299263399484729925304320, coefficient := 9282519299263399484729925304320 }, { argument := 1117627741717332379432365588480, coefficient := 1117627741717332379432365588480 }, { argument := 900311236383406638987183390720, coefficient := 900311236383406638987183390720 }, { argument := 1117627741717332379432365588480, coefficient := 1117627741717332379432365588480 }, { argument := 1117627741717332379432365588480, coefficient := 1117627741717332379432365588480 }, { argument := 47871721603559070252352992706560, coefficient := 47871721603559070252352992706560 }, { argument := 1117627741717332379432365588480, coefficient := 1117627741717332379432365588480 }, { argument := 9282519299263399484729925304320, coefficient := 9282519299263399484729925304320 }, { argument := 47871721603559070252352992706560, coefficient := 47871721603559070252352992706560 }, { argument := 993446881526517670606547189760, coefficient := 993446881526517670606547189760 }, { argument := 1117627741717332379432365588480, coefficient := 1117627741717332379432365588480 }, { argument := 1117627741717332379432365588480, coefficient := 1117627741717332379432365588480 }, { argument := 1179718171812739733845274787840, coefficient := 1179718171812739733845274787840 }, { argument := 127161200835394261837638040289280, coefficient := (-127161200835394261837638040289280) }, { argument := 53966448587597046358883696640, coefficient := 53966448587597046358883696640 }, { argument := 960602784859227425188129800192, coefficient := 960602784859227425188129800192 }, { argument := 53966448587597046358883696640, coefficient := 53966448587597046358883696640 }, { argument := 854468769303619900682325196800, coefficient := 854468769303619900682325196800 }, { argument := 1458892993484706819901822599168, coefficient := 1458892993484706819901822599168 }, { argument := 53966448587597046358883696640, coefficient := 53966448587597046358883696640 }, { argument := 1458892993484706819901822599168, coefficient := 1458892993484706819901822599168 }, { argument := 1458892993484706819901822599168, coefficient := 1458892993484706819901822599168 }, { argument := 960602784859227425188129800192, coefficient := 960602784859227425188129800192 }, { argument := 53966448587597046358883696640, coefficient := 53966448587597046358883696640 }, { argument := 7368219113826583396199587381248, coefficient := (-7368219113826583396199587381248) }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 4951760157141521099596496896000, coefficient := 4951760157141521099596496896000 }] }

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


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-20079088957371903586599583357075456)
def positiveArguments : Array ℕ := #[
    125, 2042011349, 14749632243, 4084022115, 367924437, 13643148075,
    27285795129, 736349895, 5534143, 439216915, 8793322109, 439216915,
    691695, 986279, 82899801, 41449893, 493147
  ]
def positiveCoefficients : Array ℕ := #[
    4951760157141521099596496896000, 38572503808628118455883048943616, 139306337877993252419802293600256, 38572498302348799429876729774080, 6949896118069937438555381956608, 257711780760830082292678184140800,
    257707048751274854627648961773568, 6954628127625165103584604323840, 52268502829215333943718445056, 8296572952421623671616291471360, 83050579201236442045158132809728, 8296572952421623671616291471360,
    52262996549896307937399275520, 9315141784716381623437754368, 782966483357926994312001748992, 782966341686932508222645338112, 9315283455710867712794165248
  ]
def positiveScales : Array ℕ := #[
    6, 30, 33, 31, 28, 33,
    34, 29, 22, 28, 33, 28,
    19, 19, 26, 25, 18
  ]
def negativeArguments : Array ℕ := #[
    125, 683, 6681, 1259, 5
  ]
def negativeCoefficients : Array ℕ := #[
    9903520314283042199192993792000, 216451339988970170305562072317952, 529323353757800039462467132194816, 99748256605458801030271833473024, 1584563250285286751870879006720
  ]
def negativeScales : Array ℕ := #[
    6, 9, 12, 10, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6965784283824454, 30927343737933761, 33779959932622355, 31927343531986996, 28454834260274938, 33667457524917238,
    34667431034434827, 29455816220802561, 22399928492405651, 28710358375177421, 33033761171199047, 28710358375177421,
    19399776502203236, 19911636290058366, 26304865302764193, 25304865041721014, 18911658231376114
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6965784298236803, 9415741768290103, 12705848343591960, 10298062567719017, 2321928094887363
  ]

abbrev PositiveTerm := Fin 17
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
noncomputable def positiveFloor : ℝ := 171171208211 / 500000000000
noncomputable def negativeCeiling : ℝ := 3710210373 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4951760157141521099596496896000, coefficient := 4951760157141521099596496896000 }, { argument := 9903520314283042199192993792000, coefficient := (-9903520314283042199192993792000) }, { argument := 38572503808628118455883048943616, coefficient := 38572503808628118455883048943616 }, { argument := 139306337877993252419802293600256, coefficient := 139306337877993252419802293600256 }, { argument := 38572498302348799429876729774080, coefficient := 38572498302348799429876729774080 }, { argument := 216451339988970170305562072317952, coefficient := (-216451339988970170305562072317952) }, { argument := 6949896118069937438555381956608, coefficient := 6949896118069937438555381956608 }, { argument := 257711780760830082292678184140800, coefficient := 257711780760830082292678184140800 }, { argument := 257707048751274854627648961773568, coefficient := 257707048751274854627648961773568 }, { argument := 6954628127625165103584604323840, coefficient := 6954628127625165103584604323840 }, { argument := 529323353757800039462467132194816, coefficient := (-529323353757800039462467132194816) }, { argument := 52268502829215333943718445056, coefficient := 52268502829215333943718445056 }, { argument := 8296572952421623671616291471360, coefficient := 8296572952421623671616291471360 }, { argument := 83050579201236442045158132809728, coefficient := 83050579201236442045158132809728 }, { argument := 8296572952421623671616291471360, coefficient := 8296572952421623671616291471360 }, { argument := 52262996549896307937399275520, coefficient := 52262996549896307937399275520 }, { argument := 99748256605458801030271833473024, coefficient := (-99748256605458801030271833473024) }, { argument := 9315141784716381623437754368, coefficient := 9315141784716381623437754368 }, { argument := 782966483357926994312001748992, coefficient := 782966483357926994312001748992 }, { argument := 782966341686932508222645338112, coefficient := 782966341686932508222645338112 }, { argument := 9315283455710867712794165248, coefficient := 9315283455710867712794165248 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19
