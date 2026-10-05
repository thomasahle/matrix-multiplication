import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
parent chunk 14, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14

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
def constantNumerator : ℤ := (-980141656726783314084465764990976)
def positiveArguments : Array ℕ := #[
    9, 9, 9, 4495, 108895, 82505,
    45965, 4495, 45965, 91785, 4495, 108895,
    4495, 1077, 3231, 6821, 17591, 14719,
    411773, 12565, 14719, 13283, 6821, 6821,
    13283, 411773, 13283, 1077, 17591, 801,
    12015, 21093, 801, 6675, 801, 21093,
    41919, 6675, 646941, 41385, 12015, 21093,
    801, 41385, 801, 21093, 21093, 801,
    27, 123, 3, 1287, 57, 3,
    57, 111, 2097, 111, 1287, 2097
  ]
def positiveCoefficients : Array ℕ := #[
    356526731314189519170947776512, 356526731314189519170947776512, 356526731314189519170947776512, 86945944946684130244868177920, 2106335634030960703674064568320, 1595878795956879680946128814080,
    1778184809554765760491820154880, 86945944946684130244868177920, 1778184809554765760491820154880, 1775380101653259820806501826560, 86945944946684130244868177920, 2106335634030960703674064568320,
    86945944946684130244868177920, 666630711155177278033178394624, 499973033366382958524883795968, 527749312997848678442932895744, 680518850970910137992202944512, 9110619719120756133120104726528,
    15929696368645590373001158721536, 486084893550650098565859246080, 9110619719120756133120104726528, 513861173182115818483908345856, 527749312997848678442932895744, 527749312997848678442932895744,
    513861173182115818483908345856, 15929696368645590373001158721536, 513861173182115818483908345856, 666630711155177278033178394624, 680518850970910137992202944512, 30987186608362175006068703232,
    464807799125432625091030548480, 815995914020203941826475851776, 30987186608362175006068703232, 516453110139369583434478387200, 30987186608362175006068703232, 815995914020203941826475851776,
    810831382918810245992131067904, 516453110139369583434478387200, 12513658858676925006617411321856, 800502320716022854323441500160, 464807799125432625091030548480, 815995914020203941826475851776,
    30987186608362175006068703232, 800502320716022854323441500160, 30987186608362175006068703232, 815995914020203941826475851776, 815995914020203941826475851776, 30987186608362175006068703232,
    4178047632588158427784544256, 4758332026003180431643508736, 3713820117856140824697372672, 49788400955008887931099152384, 4410161389954167229328130048, 3713820117856140824697372672,
    4410161389954167229328130048, 4294104511271162828556337152, 162247516398840152278966468608, 4294104511271162828556337152, 49788400955008887931099152384, 162247516398840152278966468608
  ]
def positiveScales : Array ℕ := #[
    3, 3, 3, 12, 16, 16,
    15, 12, 15, 16, 12, 16,
    12, 10, 11, 12, 14, 13,
    18, 13, 13, 13, 12, 12,
    13, 18, 13, 10, 14, 9,
    13, 14, 9, 12, 9, 14,
    15, 12, 19, 15, 13, 14,
    9, 15, 9, 14, 14, 9,
    4, 6, 1, 10, 5, 1,
    5, 6, 11, 6, 10, 11
  ]
def negativeArguments : Array ℕ := #[
    9, 145, 359, 267
  ]
def negativeCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 11488083564568328951063872798720, 56885820685241794392164556341248, 21153919391308578137476234739712
  ]
def negativeScales : Array ℕ := #[
    3, 7, 8, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 3169925001442312, 3169925001442312, 12134105400401809, 16732578187519716, 16332193932321516,
    15488248120154329, 12134105400401809, 15488248120154329, 16485970779443264, 12134105400401809, 16732578187519716,
    12134105400401809, 10072802534544207, 11657765035263752, 12735767547256446, 14102549877938259, 13845392038342980,
    18651489709837500, 13617123050767456, 13845392038342980, 13697293399447783, 12735767547256446, 12735767547256446,
    13697293399447783, 18651489709837500, 13697293399447783, 10072802534544207, 14102549877938259, 9645658432407524,
    13552549028017138, 14364476679864656, 9645658432407524, 12704552121457278, 9645658432407524, 14364476679864656,
    15355316680579180, 12704552121457278, 19303274621138900, 15336820336961791, 13552549028017138, 14364476679864656,
    9645658432407524, 15336820336961791, 9645658432407524, 14364476679864656, 14364476679864656, 9645658432407524,
    4754887502147955, 6942514504772358, 1584962500720924, 10329796338220701, 5832890014087662, 1584962500720924,
    5832890014087662, 6794415866314396, 11034111146096592, 6794415866314396, 10329796338220701, 11034111146096592
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 7179909090014935, 8487840033823231, 8060695931687554
  ]

abbrev PositiveTerm := Fin 60
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 3589054781 / 200000000000
noncomputable def negativeCeiling : ℝ := 8911724497 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 356526731314189519170947776512, coefficient := 356526731314189519170947776512 }, { argument := 356526731314189519170947776512, coefficient := 356526731314189519170947776512 }, { argument := 356526731314189519170947776512, coefficient := 356526731314189519170947776512 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 86945944946684130244868177920, coefficient := 86945944946684130244868177920 }, { argument := 2106335634030960703674064568320, coefficient := 2106335634030960703674064568320 }, { argument := 1595878795956879680946128814080, coefficient := 1595878795956879680946128814080 }, { argument := 1778184809554765760491820154880, coefficient := 1778184809554765760491820154880 }, { argument := 86945944946684130244868177920, coefficient := 86945944946684130244868177920 }, { argument := 1778184809554765760491820154880, coefficient := 1778184809554765760491820154880 }, { argument := 1775380101653259820806501826560, coefficient := 1775380101653259820806501826560 }, { argument := 86945944946684130244868177920, coefficient := 86945944946684130244868177920 }, { argument := 2106335634030960703674064568320, coefficient := 2106335634030960703674064568320 }, { argument := 86945944946684130244868177920, coefficient := 86945944946684130244868177920 }, { argument := 11488083564568328951063872798720, coefficient := (-11488083564568328951063872798720) }, { argument := 666630711155177278033178394624, coefficient := 666630711155177278033178394624 }, { argument := 499973033366382958524883795968, coefficient := 499973033366382958524883795968 }, { argument := 527749312997848678442932895744, coefficient := 527749312997848678442932895744 }, { argument := 680518850970910137992202944512, coefficient := 680518850970910137992202944512 }, { argument := 9110619719120756133120104726528, coefficient := 9110619719120756133120104726528 }, { argument := 15929696368645590373001158721536, coefficient := 15929696368645590373001158721536 }, { argument := 486084893550650098565859246080, coefficient := 486084893550650098565859246080 }, { argument := 9110619719120756133120104726528, coefficient := 9110619719120756133120104726528 }, { argument := 513861173182115818483908345856, coefficient := 513861173182115818483908345856 }, { argument := 527749312997848678442932895744, coefficient := 527749312997848678442932895744 }, { argument := 527749312997848678442932895744, coefficient := 527749312997848678442932895744 }, { argument := 513861173182115818483908345856, coefficient := 513861173182115818483908345856 }, { argument := 15929696368645590373001158721536, coefficient := 15929696368645590373001158721536 }, { argument := 513861173182115818483908345856, coefficient := 513861173182115818483908345856 }, { argument := 666630711155177278033178394624, coefficient := 666630711155177278033178394624 }, { argument := 680518850970910137992202944512, coefficient := 680518850970910137992202944512 }, { argument := 56885820685241794392164556341248, coefficient := (-56885820685241794392164556341248) }, { argument := 30987186608362175006068703232, coefficient := 30987186608362175006068703232 }, { argument := 464807799125432625091030548480, coefficient := 464807799125432625091030548480 }, { argument := 815995914020203941826475851776, coefficient := 815995914020203941826475851776 }, { argument := 30987186608362175006068703232, coefficient := 30987186608362175006068703232 }, { argument := 516453110139369583434478387200, coefficient := 516453110139369583434478387200 }, { argument := 30987186608362175006068703232, coefficient := 30987186608362175006068703232 }, { argument := 815995914020203941826475851776, coefficient := 815995914020203941826475851776 }, { argument := 810831382918810245992131067904, coefficient := 810831382918810245992131067904 }, { argument := 516453110139369583434478387200, coefficient := 516453110139369583434478387200 }, { argument := 12513658858676925006617411321856, coefficient := 12513658858676925006617411321856 }, { argument := 800502320716022854323441500160, coefficient := 800502320716022854323441500160 }, { argument := 464807799125432625091030548480, coefficient := 464807799125432625091030548480 }, { argument := 815995914020203941826475851776, coefficient := 815995914020203941826475851776 }, { argument := 30987186608362175006068703232, coefficient := 30987186608362175006068703232 }, { argument := 800502320716022854323441500160, coefficient := 800502320716022854323441500160 }, { argument := 30987186608362175006068703232, coefficient := 30987186608362175006068703232 }, { argument := 815995914020203941826475851776, coefficient := 815995914020203941826475851776 }, { argument := 815995914020203941826475851776, coefficient := 815995914020203941826475851776 }, { argument := 30987186608362175006068703232, coefficient := 30987186608362175006068703232 }, { argument := 21153919391308578137476234739712, coefficient := (-21153919391308578137476234739712) }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4758332026003180431643508736, coefficient := 4758332026003180431643508736 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 49788400955008887931099152384, coefficient := 49788400955008887931099152384 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 162247516398840152278966468608, coefficient := 162247516398840152278966468608 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 49788400955008887931099152384, coefficient := 49788400955008887931099152384 }, { argument := 162247516398840152278966468608, coefficient := 162247516398840152278966468608 }] }

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
def constantNumerator : ℤ := (-6456842416645716124825387135926272)
def positiveArguments : Array ℕ := #[
    27, 111, 111, 123, 8388607, 8388609,
    29946073, 53940003, 29946081, 22701957, 887462047, 887461939,
    22701993, 120353, 606011211, 24095348095, 2424048725, 120353,
    29610587, 5322321317, 10644643643, 59220165, 3198807, 144580257,
    401985
  ]
def positiveCoefficients : Array ℕ := #[
    4178047632588158427784544256, 4294104511271162828556337152, 4294104511271162828556337152, 4758332026003180431643508736, 79228153069531371854253522944, 79228171958997303332834377728,
    282832662857535290106882031616, 1018897849012352445742791524352, 282832738415399016021205450752, 214413921664695844493164806144, 8381842051143371551020809191424, 8381841031112211251177443033088,
    214414261675082611107620192256, 72748924584039732531706200064, 11447228124278577804369066983424, 113787064236904955933155781509120, 11447246451782897821462141337600, 72748924584039732531706200064,
    279664087173791278518557999104, 50267903596926856106162482315264, 50267908361794637321634502934528, 279659322306010063046537379840, 120847511695750409576698085376, 5462087677931835219959900798976,
    121492511399446677198565539840
  ]
def positiveScales : Array ℕ := #[
    4, 6, 6, 6, 22, 23,
    24, 25, 24, 24, 29, 29,
    24, 16, 29, 34, 31, 16,
    24, 32, 33, 25, 21, 27,
    18
  ]
def negativeArguments : Array ℕ := #[
    3, 1, 5, 217, 1727, 319,
    9
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 158456325028528675187087900672, 1584563250285286751870879006720, 17192511265595361257799037222912, 136827036662134511024050402230272, 101095135368201294769362080628736,
    5704427701027032306735164424192
  ]
def negativeScales : Array ℕ := #[
    1, 0, 2, 7, 10, 8,
    3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4754887502147955, 6794415866314396, 6794415866314396, 6942514504772358, 22999999826557761, 23000000171982640,
    24835863490687111, 25684852266020793, 24835863876098539, 24436313333203463, 29725110181946904, 29725110006377622,
    24436315620978931, 16876912578108937, 29174769242408503, 34488035592089000, 31174771552223433, 16876912578108937,
    24819609754924135, 32309408464769011, 33309408601521298, 25819585174329102, 21609102519407016, 27107295319182915,
    18616782142931597
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 0, 2321928094887363, 7761551232733342, 10754052367774567, 8317412613764870,
    3169925001442313
  ]

abbrev PositiveTerm := Fin 25
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 51975778533 / 500000000000
noncomputable def negativeCeiling : ℝ := 1485524487 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4758332026003180431643508736, coefficient := 4758332026003180431643508736 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 79228153069531371854253522944, coefficient := 79228153069531371854253522944 }, { argument := 79228171958997303332834377728, coefficient := 79228171958997303332834377728 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 282832662857535290106882031616, coefficient := 282832662857535290106882031616 }, { argument := 1018897849012352445742791524352, coefficient := 1018897849012352445742791524352 }, { argument := 282832738415399016021205450752, coefficient := 282832738415399016021205450752 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 214413921664695844493164806144, coefficient := 214413921664695844493164806144 }, { argument := 8381842051143371551020809191424, coefficient := 8381842051143371551020809191424 }, { argument := 8381841031112211251177443033088, coefficient := 8381841031112211251177443033088 }, { argument := 214414261675082611107620192256, coefficient := 214414261675082611107620192256 }, { argument := 17192511265595361257799037222912, coefficient := (-17192511265595361257799037222912) }, { argument := 72748924584039732531706200064, coefficient := 72748924584039732531706200064 }, { argument := 11447228124278577804369066983424, coefficient := 11447228124278577804369066983424 }, { argument := 113787064236904955933155781509120, coefficient := 113787064236904955933155781509120 }, { argument := 11447246451782897821462141337600, coefficient := 11447246451782897821462141337600 }, { argument := 72748924584039732531706200064, coefficient := 72748924584039732531706200064 }, { argument := 136827036662134511024050402230272, coefficient := (-136827036662134511024050402230272) }, { argument := 279664087173791278518557999104, coefficient := 279664087173791278518557999104 }, { argument := 50267903596926856106162482315264, coefficient := 50267903596926856106162482315264 }, { argument := 50267908361794637321634502934528, coefficient := 50267908361794637321634502934528 }, { argument := 279659322306010063046537379840, coefficient := 279659322306010063046537379840 }, { argument := 101095135368201294769362080628736, coefficient := (-101095135368201294769362080628736) }, { argument := 120847511695750409576698085376, coefficient := 120847511695750409576698085376 }, { argument := 5462087677931835219959900798976, coefficient := 5462087677931835219959900798976 }, { argument := 121492511399446677198565539840, coefficient := 121492511399446677198565539840 }, { argument := 5704427701027032306735164424192, coefficient := (-5704427701027032306735164424192) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14
