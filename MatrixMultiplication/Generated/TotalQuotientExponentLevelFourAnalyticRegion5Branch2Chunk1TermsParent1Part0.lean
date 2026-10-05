import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-773169391987540061809803264)
def positiveArguments : Array ℕ := #[
    3, 189191, 5359507, 1515573, 407831, 4092347,
    8184677, 407859, 46973, 1348989, 13985335, 674463,
    46993
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 28589735592338913523979517952, 101238224886020974441280831488, 28628364550168787221827551232, 7703709780300841108587413504, 309208996945154303701330952192,
    309208354703312633429581889536, 7704238685346922508851347456, 443647441599671689245884416, 12740840878719679654357106688, 132087754511407499289370296320, 12740245860542838079060180992,
    443836336258986475054432256
  ]
def positiveScales : Array ℕ := #[
    1, 17, 22, 20, 18, 21,
    22, 18, 15, 20, 23, 19,
    15
  ]
def negativeArguments : Array ℕ := #[
    8886868843, 255216577899, 2645899513985, 127602329433, 8890652663, 10102022965,
    3340319742173, 3340310000095, 20205713127, 8886868843, 251752122311, 71191010529,
    251752122311, 7229915988423, 74954500829845, 3614789169741, 251859312451, 3340319742173,
    66988041509275, 33493951887253, 3340547954073, 255216577899, 7229915988423, 2044491305697,
    71191010529, 2044491305697, 21195796121955, 1022197912299, 71221321989, 3340310000095,
    33493951887253, 66987766038345, 3340538212667, 2645899513985, 74954500829845, 21195796121955,
    20205713127, 3340547954073, 3340538212667, 5051845081, 127602329433, 3614789169741,
    1022197912299, 8890652663, 251859312451, 71221321989, 1, 1,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    40022899209825270919856128, 1149393285124709564918267904, 11916072065242622469928386560, 1149339606572132148273217536, 40039940020167307950030848, 45495466860862193155440640,
    1880432843268579259083390976, 1880427358966222932295024640, 45499221054756169759850496, 40022899209825270919856128, 141723845528693891538092032, 40076976061316682164994048,
    141723845528693891538092032, 4070080868922726759033470976, 42195632750878934400908656640, 4069890789467118053709840384, 141784188213014115450355712, 1880432843268579259083390976,
    75421829694862552116861337600, 75421674619298966026525343744, 1880561315147054448195403776, 1149393285124709564918267904, 4070080868922726759033470976, 1150946285312403503226814464,
    40076976061316682164994048, 1150946285312403503226814464, 11932172439582192773848104960, 1150892534232168837547032576, 40094039896311814126829568, 1880427358966222932295024640,
    75421674619298966026525343744, 75421519542168127265864417280, 1880555831223000490106159104, 11916072065242622469928386560, 42195632750878934400908656640, 11932172439582192773848104960,
    45499221054756169759850496, 1880561315147054448195403776, 1880555831223000490106159104, 45502975248650146364260352, 1149339606572132148273217536, 4069890789467118053709840384,
    1150892534232168837547032576, 40039940020167307950030848, 141784188213014115450355712, 40094039896311814126829568, 158456325028528675187087900672, 633825300114114700748351602688,
    158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    33, 37, 41, 36, 33, 33,
    41, 41, 34, 33, 37, 36,
    37, 42, 46, 41, 37, 41,
    45, 44, 41, 37, 42, 40,
    36, 40, 44, 39, 36, 41,
    44, 45, 41, 41, 46, 44,
    34, 41, 41, 32, 36, 41,
    39, 33, 37, 36, 0, 0,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 17529483934339234, 22353668868259713, 20531431912836385, 18637611915917047, 21964497048375919,
    22964494051826405, 18637710962028093, 15519544115936472, 20363447153555385, 23737411476259634, 19363379775756165,
    15520158250863009
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33049028050275784, 37892931091740280, 41266895410609484, 36892863713936376, 33049642185202322, 33233925175447909,
    41603123345655881, 41603119138014337, 34234044218812758, 33049028050275784, 37873212986876567, 36050976028772938,
    37873212986876567, 42717116021922820, 46091080344529919, 41717048644123433, 37873827121833774, 41603123345655881,
    45928968814066927, 44928965847724084, 41603221907756361, 37892931091740280, 42717116021922820, 40894879070375154,
    36050976028772938, 40894879070375154, 44268843389106637, 39894811692571094, 36051590163699475, 41603119138014337,
    44928965847724084, 45928962881345163, 41603217700692486, 41266895410609484, 46091080344529919, 44268843389106637,
    34234044218812758, 41603221907756361, 41603217700692486, 32234163252355606, 36892863713936376, 41717048644123433,
    39894811692571094, 33049642185202322, 37873827121833774, 36051590163699475, 0, 0,
    0
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 52819521 / 200000000000
noncomputable def negativeCeiling : ℝ := 256926421 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 40022899209825270919856128, coefficient := (-40022899209825270919856128) }, { argument := 1149393285124709564918267904, coefficient := (-1149393285124709564918267904) }, { argument := 11916072065242622469928386560, coefficient := (-11916072065242622469928386560) }, { argument := 1149339606572132148273217536, coefficient := (-1149339606572132148273217536) }, { argument := 40039940020167307950030848, coefficient := (-40039940020167307950030848) }, { argument := 45495466860862193155440640, coefficient := (-45495466860862193155440640) }, { argument := 1880432843268579259083390976, coefficient := (-1880432843268579259083390976) }, { argument := 1880427358966222932295024640, coefficient := (-1880427358966222932295024640) }, { argument := 45499221054756169759850496, coefficient := (-45499221054756169759850496) }, { argument := 40022899209825270919856128, coefficient := (-40022899209825270919856128) }, { argument := 141723845528693891538092032, coefficient := (-141723845528693891538092032) }, { argument := 40076976061316682164994048, coefficient := (-40076976061316682164994048) }, { argument := 141723845528693891538092032, coefficient := (-141723845528693891538092032) }, { argument := 4070080868922726759033470976, coefficient := (-4070080868922726759033470976) }, { argument := 42195632750878934400908656640, coefficient := (-42195632750878934400908656640) }, { argument := 4069890789467118053709840384, coefficient := (-4069890789467118053709840384) }, { argument := 141784188213014115450355712, coefficient := (-141784188213014115450355712) }, { argument := 1880432843268579259083390976, coefficient := (-1880432843268579259083390976) }, { argument := 75421829694862552116861337600, coefficient := (-75421829694862552116861337600) }, { argument := 75421674619298966026525343744, coefficient := (-75421674619298966026525343744) }, { argument := 1880561315147054448195403776, coefficient := (-1880561315147054448195403776) }, { argument := 1149393285124709564918267904, coefficient := (-1149393285124709564918267904) }, { argument := 4070080868922726759033470976, coefficient := (-4070080868922726759033470976) }, { argument := 1150946285312403503226814464, coefficient := (-1150946285312403503226814464) }, { argument := 40076976061316682164994048, coefficient := (-40076976061316682164994048) }, { argument := 1150946285312403503226814464, coefficient := (-1150946285312403503226814464) }, { argument := 11932172439582192773848104960, coefficient := (-11932172439582192773848104960) }, { argument := 1150892534232168837547032576, coefficient := (-1150892534232168837547032576) }, { argument := 40094039896311814126829568, coefficient := (-40094039896311814126829568) }, { argument := 1880427358966222932295024640, coefficient := (-1880427358966222932295024640) }, { argument := 75421674619298966026525343744, coefficient := (-75421674619298966026525343744) }, { argument := 75421519542168127265864417280, coefficient := (-75421519542168127265864417280) }, { argument := 1880555831223000490106159104, coefficient := (-1880555831223000490106159104) }, { argument := 11916072065242622469928386560, coefficient := (-11916072065242622469928386560) }, { argument := 42195632750878934400908656640, coefficient := (-42195632750878934400908656640) }, { argument := 11932172439582192773848104960, coefficient := (-11932172439582192773848104960) }, { argument := 45499221054756169759850496, coefficient := (-45499221054756169759850496) }, { argument := 1880561315147054448195403776, coefficient := (-1880561315147054448195403776) }, { argument := 1880555831223000490106159104, coefficient := (-1880555831223000490106159104) }, { argument := 45502975248650146364260352, coefficient := (-45502975248650146364260352) }, { argument := 1149339606572132148273217536, coefficient := (-1149339606572132148273217536) }, { argument := 4069890789467118053709840384, coefficient := (-4069890789467118053709840384) }, { argument := 1150892534232168837547032576, coefficient := (-1150892534232168837547032576) }, { argument := 40039940020167307950030848, coefficient := (-40039940020167307950030848) }, { argument := 141784188213014115450355712, coefficient := (-141784188213014115450355712) }, { argument := 40094039896311814126829568, coefficient := (-40094039896311814126829568) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 28589735592338913523979517952, coefficient := 28589735592338913523979517952 }, { argument := 101238224886020974441280831488, coefficient := 101238224886020974441280831488 }, { argument := 28628364550168787221827551232, coefficient := 28628364550168787221827551232 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 7703709780300841108587413504, coefficient := 7703709780300841108587413504 }, { argument := 309208996945154303701330952192, coefficient := 309208996945154303701330952192 }, { argument := 309208354703312633429581889536, coefficient := 309208354703312633429581889536 }, { argument := 7704238685346922508851347456, coefficient := 7704238685346922508851347456 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 443647441599671689245884416, coefficient := 443647441599671689245884416 }, { argument := 12740840878719679654357106688, coefficient := 12740840878719679654357106688 }, { argument := 132087754511407499289370296320, coefficient := 132087754511407499289370296320 }, { argument := 12740245860542838079060180992, coefficient := 12740245860542838079060180992 }, { argument := 443836336258986475054432256, coefficient := 443836336258986475054432256 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1
