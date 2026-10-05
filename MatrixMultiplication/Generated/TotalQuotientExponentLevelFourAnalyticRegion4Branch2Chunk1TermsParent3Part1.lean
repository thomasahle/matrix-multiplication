import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 4, branch 2,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1

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
def constantNumerator : ℤ := 199464247382226025982977766326272
def positiveArguments : Array ℕ := #[
    5, 3050209, 5336423, 3054161, 238019, 73593281,
    73593335, 119011, 93815, 10156091, 137, 114492997,
    61, 19
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 28808409494694675315244924928, 100802180454458722880828997632, 28845735079375276991013978112, 17984207166178401345899331584, 695068887117614973163669553152,
    695069397133195123085352632320, 17984433839769579088869588992, 3544230492723326125783121920, 95921567470748115856022044672, 5299930793190534301911875584, 1081355783112189681685520973824,
    4719646399775512298052911104, 735026898325694538221355008
  ]
def positiveScales : Array ℕ := #[
    2, 21, 22, 21, 17, 26,
    26, 16, 16, 23, 7, 26,
    5, 4
  ]
def negativeArguments : Array ℕ := #[
    550122105, 13953201, 1071587106891, 3888597, 4346079, 13953201,
    4346079, 31337517, 3888597, 81191251587, 2143143845753, 83052677209209,
    10381592807535, 1071587106891, 25051534278495, 43828335602265, 25083992271855, 3888665,
    138717705, 138717705, 3888597, 4346155, 155037435, 155037435,
    4346079, 13953445, 497751765, 497751765, 13953201, 4346155,
    155037435, 155037435, 4346079, 31338065, 1117901505, 1117901505,
    31337517, 3888665, 138717705, 138717705, 3888597, 10148807671,
    3112594423779, 1556298266865, 81191251587, 267762597065, 468457893055, 268109523385,
    1, 9
  ]
def negativeCoefficients : Array ℕ := #[
    634247605014085855850004480, 32173890982003523664740352, 603249911911166933301460992, 35865976832397370642661376, 5010687939820220898607104, 32173890982003523664740352,
    5010687939820220898607104, 36129697250282645426798592, 35865976832397370642661376, 22853305649559836999811072, 603241364070911409775443968, 23377250383219733628771631104,
    23377268749763423699132743680, 603249911911166933301460992, 7051380027605580585338142720, 24673159485828712172806471680, 7060516140530661212427386880, 35866604021695876767416320,
    1279445001313669918375280640, 1279445001313669918375280640, 35865976832397370642661376, 5010775561854571018977280, 178745992830586238596546560, 178745992830586238596546560,
    5010687939820220898607104, 32174453607697771806064640, 1147737427649027426777825280, 1147737427649027426777825280, 32173890982003523664740352, 5010775561854571018977280,
    178745992830586238596546560, 178745992830586238596546560, 5010687939820220898607104, 36130329051267169978941440, 1288852685146858667775098880, 1288852685146858667775098880,
    36129697250282645426798592, 35866604021695876767416320, 1279445001313669918375280640, 1279445001313669918375280640, 35865976832397370642661376, 22853083222685215681937408,
    876117442942911757129089024, 876118036841320342754426880, 22853305649559836999811072, 150736941545711283239649280, 527436698150316416507576320, 150932243701395910421381120,
    158456325028528675187087900672, 1426106925256758076683791106048
  ]
def negativeScales : Array ℕ := #[
    29, 23, 39, 21, 22, 23,
    22, 24, 21, 36, 40, 46,
    43, 39, 44, 45, 44, 21,
    27, 27, 21, 22, 27, 27,
    22, 23, 28, 28, 23, 22,
    27, 27, 22, 24, 30, 30,
    24, 21, 27, 27, 21, 33,
    41, 40, 36, 37, 38, 37,
    0, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 21540476668699025, 22347441597880975, 21542344685086678, 17860717216375233, 26133070719753760,
    26133071778349091, 16860735400040556, 16517530992007411, 23275841891117445, 7098032082960526, 26770684117204175,
    5930737337099561, 4247927513443585
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29035176633602142, 23734092792665833, 39962886279781576, 21890818299896343, 22051282968388323, 23734092792665833,
    22051282968388323, 24901387542382794, 21890818299896343, 36240605233279116, 40962865837148221, 46239091907854564,
    43239093041320248, 39962886279781576, 44509964197363439, 45316929126544951, 44511832213751120, 21890843528124315,
    27047576694457359, 27047576694457359, 21890818299896343, 22051308196614602, 27208041366650605, 27208041366650605,
    22051282968388323, 23734118020892201, 28890851194473380, 28890851194473380, 23734092792665833, 22051308196614602,
    27208041366650605, 27208041366650605, 22051282968388323, 24901412770611095, 30058145936167546, 30058145936167546,
    24901387542382794, 21890843528124315, 27047576694457359, 27047576694457359, 21890818299896343, 33240591191734513,
    41501254742143061, 40501255720110119, 36240605233279116, 37962163505639011, 38769128422378346, 37964031522429984,
    0, 3169925001442313
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 50
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
noncomputable def positiveFloor : ℝ := 90802123 / 100000000000
noncomputable def negativeCeiling : ℝ := 53378093 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 634247605014085855850004480, coefficient := (-634247605014085855850004480) }, { argument := 32173890982003523664740352, coefficient := (-32173890982003523664740352) }, { argument := 603249911911166933301460992, coefficient := (-603249911911166933301460992) }, { argument := 35865976832397370642661376, coefficient := (-35865976832397370642661376) }, { argument := 5010687939820220898607104, coefficient := (-5010687939820220898607104) }, { argument := 32173890982003523664740352, coefficient := (-32173890982003523664740352) }, { argument := 5010687939820220898607104, coefficient := (-5010687939820220898607104) }, { argument := 36129697250282645426798592, coefficient := (-36129697250282645426798592) }, { argument := 35865976832397370642661376, coefficient := (-35865976832397370642661376) }, { argument := 22853305649559836999811072, coefficient := (-22853305649559836999811072) }, { argument := 603241364070911409775443968, coefficient := (-603241364070911409775443968) }, { argument := 23377250383219733628771631104, coefficient := (-23377250383219733628771631104) }, { argument := 23377268749763423699132743680, coefficient := (-23377268749763423699132743680) }, { argument := 603249911911166933301460992, coefficient := (-603249911911166933301460992) }, { argument := 7051380027605580585338142720, coefficient := (-7051380027605580585338142720) }, { argument := 24673159485828712172806471680, coefficient := (-24673159485828712172806471680) }, { argument := 7060516140530661212427386880, coefficient := (-7060516140530661212427386880) }, { argument := 35866604021695876767416320, coefficient := (-35866604021695876767416320) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 35865976832397370642661376, coefficient := (-35865976832397370642661376) }, { argument := 5010775561854571018977280, coefficient := (-5010775561854571018977280) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 5010687939820220898607104, coefficient := (-5010687939820220898607104) }, { argument := 32174453607697771806064640, coefficient := (-32174453607697771806064640) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 32173890982003523664740352, coefficient := (-32173890982003523664740352) }, { argument := 5010775561854571018977280, coefficient := (-5010775561854571018977280) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 5010687939820220898607104, coefficient := (-5010687939820220898607104) }, { argument := 36130329051267169978941440, coefficient := (-36130329051267169978941440) }, { argument := 1288852685146858667775098880, coefficient := (-1288852685146858667775098880) }, { argument := 1288852685146858667775098880, coefficient := (-1288852685146858667775098880) }, { argument := 36129697250282645426798592, coefficient := (-36129697250282645426798592) }, { argument := 35866604021695876767416320, coefficient := (-35866604021695876767416320) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 35865976832397370642661376, coefficient := (-35865976832397370642661376) }, { argument := 22853083222685215681937408, coefficient := (-22853083222685215681937408) }, { argument := 876117442942911757129089024, coefficient := (-876117442942911757129089024) }, { argument := 876118036841320342754426880, coefficient := (-876118036841320342754426880) }, { argument := 22853305649559836999811072, coefficient := (-22853305649559836999811072) }, { argument := 150736941545711283239649280, coefficient := (-150736941545711283239649280) }, { argument := 527436698150316416507576320, coefficient := (-527436698150316416507576320) }, { argument := 150932243701395910421381120, coefficient := (-150932243701395910421381120) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 28808409494694675315244924928, coefficient := 28808409494694675315244924928 }, { argument := 100802180454458722880828997632, coefficient := 100802180454458722880828997632 }, { argument := 28845735079375276991013978112, coefficient := 28845735079375276991013978112 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 17984207166178401345899331584, coefficient := 17984207166178401345899331584 }, { argument := 695068887117614973163669553152, coefficient := 695068887117614973163669553152 }, { argument := 695069397133195123085352632320, coefficient := 695069397133195123085352632320 }, { argument := 17984433839769579088869588992, coefficient := 17984433839769579088869588992 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 3544230492723326125783121920, coefficient := 3544230492723326125783121920 }, { argument := 95921567470748115856022044672, coefficient := 95921567470748115856022044672 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 1081355783112189681685520973824, coefficient := 1081355783112189681685520973824 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }] }

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
def constantNumerator : ℤ := (-123237882599932166120068442226688)
def positiveArguments : Array ℕ := #[
    17, 17, 61, 2405, 61, 10156139,
    17, 19, 61, 19, 137, 17,
    380729, 173345, 4107623, 8213055, 87785
  ]
def positiveCoefficients : Array ℕ := #[
    5261245166962866168321277952, 5261245166962866168321277952, 4719646399775512298052911104, 93038931077541861285387304960, 4719646399775512298052911104, 95922020817930471341962559488,
    5261245166962866168321277952, 735026898325694538221355008, 4719646399775512298052911104, 735026898325694538221355008, 5299930793190534301911875584, 5261245166962866168321277952,
    3595883737312954305130528768, 1637197235946077299136266240, 77590804717857842726470418432, 77570111307929907941144002560, 1658211766794847220337213440
  ]
def positiveScales : Array ℕ := #[
    4, 4, 5, 11, 5, 23,
    4, 4, 5, 4, 7, 4,
    18, 17, 21, 22, 16
  ]
def negativeArguments : Array ℕ := #[
    9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 4087462841250339, 5930737337099561, 11231821178657404, 5930737337099561, 23275848709606794,
    4087462841250339, 4247927513443585, 5930737337099561, 4247927513443585, 7098032082960526, 4087462841250339,
    18538404938118767, 17403286698175498, 21969872344780066, 22969487527773511, 16421686824157693
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 10683361 / 125000000000
noncomputable def negativeCeiling : ℝ := 5441537 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 93038931077541861285387304960, coefficient := 93038931077541861285387304960 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 95922020817930471341962559488, coefficient := 95922020817930471341962559488 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 3595883737312954305130528768, coefficient := 3595883737312954305130528768 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 1637197235946077299136266240, coefficient := 1637197235946077299136266240 }, { argument := 77590804717857842726470418432, coefficient := 77590804717857842726470418432 }, { argument := 77570111307929907941144002560, coefficient := 77570111307929907941144002560 }, { argument := 1658211766794847220337213440, coefficient := 1658211766794847220337213440 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1
