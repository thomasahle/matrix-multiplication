import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-24078367906347202718091513430016)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    528738479105, 12529108643207, 25051534278495, 267762597065, 80517928503, 1071566400673,
    31338065, 11983998126251, 13953445, 4346155, 3888665, 3888665,
    13953445, 550131725, 13953445, 2143143845753, 3888665, 4346155,
    13953445, 4346155, 31338065, 3888665, 10148807671, 80517928503,
    766847433641, 1533695907835, 80518597423, 925042244935, 21920013852529, 43828335602265,
    468457893055, 766847433641, 83052285600633, 1117901505, 936468287590791, 497751765,
    155037435, 138717705, 138717705, 497751765, 19624475325, 497751765,
    83052677209209, 138717705, 155037435, 497751765, 155037435, 1117901505,
    138717705, 3112594423779, 1071566400673, 83052285600633, 41526175425645, 2143163169387,
    31338065, 1117901505, 1117901505, 31337517, 528738479105, 925042244935,
    529423538545, 529423538545, 12545341969303, 25083992271855
  ]
def negativeCoefficients : Array ℕ := #[
    148826651092107549086842880, 7053261127103938239957827584, 7051380027605580585338142720, 150736941545711283239649280, 22663782050172189926227968, 603238255346708301769342976,
    36130329051267169978941440, 6746391186974090734770061312, 32174453607697771806064640, 5010775561854571018977280, 35866604021695876767416320, 35866604021695876767416320,
    32174453607697771806064640, 634258696118960173717913600, 32174453607697771806064640, 603241364070911409775443968, 35866604021695876767416320, 5010775561854571018977280,
    32174453607697771806064640, 5010775561854571018977280, 36130329051267169978941440, 35866604021695876767416320, 22853083222685215681937408, 22663782050172189926227968,
    863393454098907189670313984, 863394039878170072076779520, 22663970334413611218239488, 520752488698904136353054720, 24679741554551428714747396096, 24673159485828712172806471680,
    527436698150316416507576320, 863393454098907189670313984, 23377140155204924335611445248, 1288852685146858667775098880, 263592389439885801932137168896, 1147737427649027426777825280,
    178745992830586238596546560, 1279445001313669918375280640, 1279445001313669918375280640, 1147737427649027426777825280, 22625479618818942306562867200, 1147737427649027426777825280,
    23377250383219733628771631104, 1279445001313669918375280640, 178745992830586238596546560, 1147737427649027426777825280, 178745992830586238596546560, 1288852685146858667775098880,
    1279445001313669918375280640, 876117442942911757129089024, 603238255346708301769342976, 23377140155204924335611445248, 23377158521632083765614346240, 603246803190341525015887872,
    36130329051267169978941440, 1288852685146858667775098880, 1288852685146858667775098880, 36129697250282645426798592, 148826651092107549086842880, 520752488698904136353054720,
    149019478182026964128235520, 149019478182026964128235520, 7062399677273554408529985536, 7060516140530661212427386880
  ]
def negativeScales : Array ℕ := #[
    38, 43, 44, 37, 36, 39,
    24, 43, 23, 22, 21, 21,
    23, 29, 23, 40, 21, 22,
    23, 22, 24, 21, 33, 36,
    39, 40, 36, 39, 44, 45,
    38, 39, 46, 30, 49, 28,
    27, 27, 27, 28, 34, 28,
    46, 27, 27, 28, 27, 30,
    27, 41, 39, 46, 45, 40,
    24, 30, 30, 24, 38, 39,
    38, 38, 43, 44
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    38943763376253070, 43510349014375663, 44509964197363439, 37962163505639011, 36228591005175449, 39962858402390296,
    24901412770611095, 43446174536873574, 23734118020892201, 22051308196614602, 21890843528124315, 21890843528124315,
    23734118020892201, 29035201861828421, 23734118020892201, 40962865837148221, 21890843528124315, 22051308196614602,
    23734118020892201, 22051308196614602, 24901412770611095, 21890843528124315, 33240591191734513, 36228591005175449,
    39480148621980210, 40480149600792995, 36228602990624852, 39750728296284962, 44317313943557170, 45316929126544951,
    38769128422378346, 39480148621980210, 46239085105267320, 30058145936167546, 49734223468687921, 28890851194473380,
    27208041366650605, 27047576694457359, 27047576694457359, 28890851194473380, 34191935031864424, 28890851194473380,
    46239091907854564, 27047576694457359, 27208041366650605, 28890851194473380, 27208041366650605, 30058145936167546,
    27047576694457359, 41501254742143061, 39962858402390296, 46239085105267320, 45239086238731157, 40962878845137077,
    24901412770611095, 30058145936167546, 30058145936167546, 24901387542382794, 38943763376253070, 39750728296284962,
    38945631392943177, 38945631392943177, 43512217030763344, 44511832213751120
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
noncomputable def negativeCeiling : ℝ := 27361563 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 148826651092107549086842880, coefficient := (-148826651092107549086842880) }, { argument := 7053261127103938239957827584, coefficient := (-7053261127103938239957827584) }, { argument := 7051380027605580585338142720, coefficient := (-7051380027605580585338142720) }, { argument := 150736941545711283239649280, coefficient := (-150736941545711283239649280) }, { argument := 22663782050172189926227968, coefficient := (-22663782050172189926227968) }, { argument := 603238255346708301769342976, coefficient := (-603238255346708301769342976) }, { argument := 36130329051267169978941440, coefficient := (-36130329051267169978941440) }, { argument := 6746391186974090734770061312, coefficient := (-6746391186974090734770061312) }, { argument := 32174453607697771806064640, coefficient := (-32174453607697771806064640) }, { argument := 5010775561854571018977280, coefficient := (-5010775561854571018977280) }, { argument := 35866604021695876767416320, coefficient := (-35866604021695876767416320) }, { argument := 35866604021695876767416320, coefficient := (-35866604021695876767416320) }, { argument := 32174453607697771806064640, coefficient := (-32174453607697771806064640) }, { argument := 634258696118960173717913600, coefficient := (-634258696118960173717913600) }, { argument := 32174453607697771806064640, coefficient := (-32174453607697771806064640) }, { argument := 603241364070911409775443968, coefficient := (-603241364070911409775443968) }, { argument := 35866604021695876767416320, coefficient := (-35866604021695876767416320) }, { argument := 5010775561854571018977280, coefficient := (-5010775561854571018977280) }, { argument := 32174453607697771806064640, coefficient := (-32174453607697771806064640) }, { argument := 5010775561854571018977280, coefficient := (-5010775561854571018977280) }, { argument := 36130329051267169978941440, coefficient := (-36130329051267169978941440) }, { argument := 35866604021695876767416320, coefficient := (-35866604021695876767416320) }, { argument := 22853083222685215681937408, coefficient := (-22853083222685215681937408) }, { argument := 22663782050172189926227968, coefficient := (-22663782050172189926227968) }, { argument := 863393454098907189670313984, coefficient := (-863393454098907189670313984) }, { argument := 863394039878170072076779520, coefficient := (-863394039878170072076779520) }, { argument := 22663970334413611218239488, coefficient := (-22663970334413611218239488) }, { argument := 520752488698904136353054720, coefficient := (-520752488698904136353054720) }, { argument := 24679741554551428714747396096, coefficient := (-24679741554551428714747396096) }, { argument := 24673159485828712172806471680, coefficient := (-24673159485828712172806471680) }, { argument := 527436698150316416507576320, coefficient := (-527436698150316416507576320) }, { argument := 863393454098907189670313984, coefficient := (-863393454098907189670313984) }, { argument := 23377140155204924335611445248, coefficient := (-23377140155204924335611445248) }, { argument := 1288852685146858667775098880, coefficient := (-1288852685146858667775098880) }, { argument := 263592389439885801932137168896, coefficient := (-263592389439885801932137168896) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 22625479618818942306562867200, coefficient := (-22625479618818942306562867200) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 23377250383219733628771631104, coefficient := (-23377250383219733628771631104) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 1288852685146858667775098880, coefficient := (-1288852685146858667775098880) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 876117442942911757129089024, coefficient := (-876117442942911757129089024) }, { argument := 603238255346708301769342976, coefficient := (-603238255346708301769342976) }, { argument := 23377140155204924335611445248, coefficient := (-23377140155204924335611445248) }, { argument := 23377158521632083765614346240, coefficient := (-23377158521632083765614346240) }, { argument := 603246803190341525015887872, coefficient := (-603246803190341525015887872) }, { argument := 36130329051267169978941440, coefficient := (-36130329051267169978941440) }, { argument := 1288852685146858667775098880, coefficient := (-1288852685146858667775098880) }, { argument := 1288852685146858667775098880, coefficient := (-1288852685146858667775098880) }, { argument := 36129697250282645426798592, coefficient := (-36129697250282645426798592) }, { argument := 148826651092107549086842880, coefficient := (-148826651092107549086842880) }, { argument := 520752488698904136353054720, coefficient := (-520752488698904136353054720) }, { argument := 149019478182026964128235520, coefficient := (-149019478182026964128235520) }, { argument := 149019478182026964128235520, coefficient := (-149019478182026964128235520) }, { argument := 7062399677273554408529985536, coefficient := (-7062399677273554408529985536) }, { argument := 7060516140530661212427386880, coefficient := (-7060516140530661212427386880) }] }

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

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-49583070175322557542828618022912)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    268109523385, 1533695907835, 41526175425645, 1117901505, 468234529433835, 497751765,
    155037435, 138717705, 138717705, 497751765, 19624475325, 497751765,
    10381592807535, 138717705, 155037435, 497751765, 155037435, 1117901505,
    138717705, 1556298266865, 11983998126251, 936468287590791, 468234529433835, 23968398445389,
    13953445, 497751765, 497751765, 13953201, 12529108643207, 21920013852529,
    12545341969303, 4346155, 155037435, 155037435, 4346079, 3888665,
    138717705, 138717705, 3888597, 3888665, 138717705, 138717705,
    3888597, 13953445, 497751765, 497751765, 13953201, 550131725,
    19624475325, 19624475325, 550122105, 13953445, 497751765, 497751765,
    13953201, 80518597423, 2143163169387, 31337517, 23968398445389, 13953201,
    4346079, 3888597, 3888597, 13953201
  ]
def negativeCoefficients : Array ℕ := #[
    150932243701395910421381120, 863394039878170072076779520, 23377158521632083765614346240, 1288852685146858667775098880, 263592606535027355924582891520, 1147737427649027426777825280,
    178745992830586238596546560, 1279445001313669918375280640, 1279445001313669918375280640, 1147737427649027426777825280, 22625479618818942306562867200, 1147737427649027426777825280,
    23377268749763423699132743680, 1279445001313669918375280640, 178745992830586238596546560, 1147737427649027426777825280, 178745992830586238596546560, 1288852685146858667775098880,
    1279445001313669918375280640, 876118036841320342754426880, 6746391186974090734770061312, 263592389439885801932137168896, 263592606535027355924582891520, 6746504394207592251270365184,
    32174453607697771806064640, 1147737427649027426777825280, 1147737427649027426777825280, 32173890982003523664740352, 7053261127103938239957827584, 24679741554551428714747396096,
    7062399677273554408529985536, 5010775561854571018977280, 178745992830586238596546560, 178745992830586238596546560, 5010687939820220898607104, 35866604021695876767416320,
    1279445001313669918375280640, 1279445001313669918375280640, 35865976832397370642661376, 35866604021695876767416320, 1279445001313669918375280640, 1279445001313669918375280640,
    35865976832397370642661376, 32174453607697771806064640, 1147737427649027426777825280, 1147737427649027426777825280, 32173890982003523664740352, 634258696118960173717913600,
    22625479618818942306562867200, 22625479618818942306562867200, 634247605014085855850004480, 32174453607697771806064640, 1147737427649027426777825280, 1147737427649027426777825280,
    32173890982003523664740352, 22663970334413611218239488, 603246803190341525015887872, 36129697250282645426798592, 6746504394207592251270365184, 32173890982003523664740352,
    5010687939820220898607104, 35865976832397370642661376, 35865976832397370642661376, 32173890982003523664740352
  ]
def negativeScales : Array ℕ := #[
    37, 40, 45, 30, 48, 28,
    27, 27, 27, 28, 34, 28,
    43, 27, 27, 28, 27, 30,
    27, 40, 43, 49, 48, 44,
    23, 28, 28, 23, 43, 44,
    43, 22, 27, 27, 22, 21,
    27, 27, 21, 21, 27, 27,
    21, 23, 28, 28, 23, 29,
    34, 34, 29, 23, 28, 28,
    23, 36, 40, 24, 44, 23,
    22, 21, 21, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37964031522429984, 40480149600792995, 45239086238731157, 30058145936167546, 48734224656893532, 28890851194473380,
    27208041366650605, 27047576694457359, 27047576694457359, 28890851194473380, 34191935031864424, 28890851194473380,
    43239093041320248, 27047576694457359, 27208041366650605, 28890851194473380, 27208041366650605, 30058145936167546,
    27047576694457359, 40501255720110119, 43446174536873574, 49734223468687921, 48734224656893532, 44446198745689745,
    23734118020892201, 28890851194473380, 28890851194473380, 23734092792665833, 43510349014375663, 44317313943557170,
    43512217030763344, 22051308196614602, 27208041366650605, 27208041366650605, 22051282968388323, 21890843528124315,
    27047576694457359, 27047576694457359, 21890818299896343, 21890843528124315, 27047576694457359, 27047576694457359,
    21890818299896343, 23734118020892201, 28890851194473380, 28890851194473380, 23734092792665833, 29035201861828421,
    34191935031864424, 34191935031864424, 29035176633602142, 23734118020892201, 28890851194473380, 28890851194473380,
    23734092792665833, 36228602990624852, 40962878845137077, 24901387542382794, 44446198745689745, 23734092792665833,
    22051282968388323, 21890818299896343, 21890818299896343, 23734092792665833
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
noncomputable def negativeCeiling : ℝ := 70194561 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 150932243701395910421381120, coefficient := (-150932243701395910421381120) }, { argument := 863394039878170072076779520, coefficient := (-863394039878170072076779520) }, { argument := 23377158521632083765614346240, coefficient := (-23377158521632083765614346240) }, { argument := 1288852685146858667775098880, coefficient := (-1288852685146858667775098880) }, { argument := 263592606535027355924582891520, coefficient := (-263592606535027355924582891520) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 22625479618818942306562867200, coefficient := (-22625479618818942306562867200) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 23377268749763423699132743680, coefficient := (-23377268749763423699132743680) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 1288852685146858667775098880, coefficient := (-1288852685146858667775098880) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 876118036841320342754426880, coefficient := (-876118036841320342754426880) }, { argument := 6746391186974090734770061312, coefficient := (-6746391186974090734770061312) }, { argument := 263592389439885801932137168896, coefficient := (-263592389439885801932137168896) }, { argument := 263592606535027355924582891520, coefficient := (-263592606535027355924582891520) }, { argument := 6746504394207592251270365184, coefficient := (-6746504394207592251270365184) }, { argument := 32174453607697771806064640, coefficient := (-32174453607697771806064640) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 32173890982003523664740352, coefficient := (-32173890982003523664740352) }, { argument := 7053261127103938239957827584, coefficient := (-7053261127103938239957827584) }, { argument := 24679741554551428714747396096, coefficient := (-24679741554551428714747396096) }, { argument := 7062399677273554408529985536, coefficient := (-7062399677273554408529985536) }, { argument := 5010775561854571018977280, coefficient := (-5010775561854571018977280) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 178745992830586238596546560, coefficient := (-178745992830586238596546560) }, { argument := 5010687939820220898607104, coefficient := (-5010687939820220898607104) }, { argument := 35866604021695876767416320, coefficient := (-35866604021695876767416320) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 35865976832397370642661376, coefficient := (-35865976832397370642661376) }, { argument := 35866604021695876767416320, coefficient := (-35866604021695876767416320) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 1279445001313669918375280640, coefficient := (-1279445001313669918375280640) }, { argument := 35865976832397370642661376, coefficient := (-35865976832397370642661376) }, { argument := 32174453607697771806064640, coefficient := (-32174453607697771806064640) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 32173890982003523664740352, coefficient := (-32173890982003523664740352) }, { argument := 634258696118960173717913600, coefficient := (-634258696118960173717913600) }, { argument := 22625479618818942306562867200, coefficient := (-22625479618818942306562867200) }, { argument := 22625479618818942306562867200, coefficient := (-22625479618818942306562867200) }, { argument := 634247605014085855850004480, coefficient := (-634247605014085855850004480) }, { argument := 32174453607697771806064640, coefficient := (-32174453607697771806064640) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 1147737427649027426777825280, coefficient := (-1147737427649027426777825280) }, { argument := 32173890982003523664740352, coefficient := (-32173890982003523664740352) }, { argument := 22663970334413611218239488, coefficient := (-22663970334413611218239488) }, { argument := 603246803190341525015887872, coefficient := (-603246803190341525015887872) }, { argument := 36129697250282645426798592, coefficient := (-36129697250282645426798592) }, { argument := 6746504394207592251270365184, coefficient := (-6746504394207592251270365184) }, { argument := 32173890982003523664740352, coefficient := (-32173890982003523664740352) }, { argument := 5010687939820220898607104, coefficient := (-5010687939820220898607104) }, { argument := 35865976832397370642661376, coefficient := (-35865976832397370642661376) }, { argument := 35865976832397370642661376, coefficient := (-35865976832397370642661376) }, { argument := 32173890982003523664740352, coefficient := (-32173890982003523664740352) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1
