import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 16, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-33480006833290302827245894268616704)
def positiveArguments : Array ℕ := #[
    3189, 164765, 3189, 83977, 83977, 3189,
    243, 1107, 27, 11583, 513, 27,
    513, 999, 18873, 999, 11583, 18873,
    243, 999, 999, 1107, 8388607, 8388609,
    154123595, 1111558799, 308247259, 453029477, 4424979829, 17699916073,
    226515279, 4060121, 1183038957, 23261699267, 2366081179, 4060121,
    55954081, 9918100831, 1239762739, 6994125, 6042191, 273096041,
    759305
  ]
def positiveCoefficients : Array ℕ := #[
    246736924080067356040831696896, 6374037205401740031054818836480, 246736924080067356040831696896, 6497405667441773709075234684928, 6497405667441773709075234684928, 246736924080067356040831696896,
    75204857386586851700121796608, 85649976468057247769583157248, 66848762121410534844552708096, 896191217190159982759784742912, 79382905019175010127906340864, 66848762121410534844552708096,
    79382905019175010127906340864, 77293881202880930914014068736, 2920455295179122741021396434944, 77293881202880930914014068736, 896191217190159982759784742912, 2920455295179122741021396434944,
    75204857386586851700121796608, 77293881202880930914014068736, 77293881202880930914014068736, 85649976468057247769583157248, 79228153069531371854253522944, 79228171958997303332834377728,
    1455656198494751273418741514240, 5249188016136436907292024111104, 1455656524338038591424261259264, 2139371217936764830336252116992, 83585505727375416427964778151936, 83585490412740912481705350135808,
    2139376322814932812422728122368, 306774069228722988714825875456, 44693948147726907524567663640576, 439401075812296776495929206243328, 44694009821833173802134154510336, 306774069228722988714825875456,
    264235676694173240728408293376, 46836906938035975458633470181376, 46836912042914143440719946186752, 264230571816005258641932288000, 28533440261496624483387047936, 1289659590622794426934976577536,
    28685731858202687671883530240
  ]
def positiveScales : Array ℕ := #[
    11, 17, 11, 16, 16, 11,
    7, 10, 4, 13, 9, 4,
    9, 9, 14, 9, 13, 14,
    7, 9, 9, 10, 22, 23,
    27, 30, 28, 28, 32, 34,
    27, 21, 30, 34, 31, 21,
    25, 33, 30, 22, 22, 28,
    19
  ]
def negativeArguments : Array ℕ := #[
    1063, 27, 1, 103, 541, 3341,
    1189, 17
  ]
def negativeCoefficients : Array ℕ := #[
    168439073505325981723874438414336, 8556641551540548460102746636288, 158456325028528675187087900672, 8160500738969226772135026884608, 171449743680868026552429108527104, 529402581920314303800060676145152,
    94202285229460297398723756949504, 1346878762742493739090247155712
  ]
def negativeScales : Array ℕ := #[
    10, 4, 0, 6, 9, 11,
    10, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11638888382251264, 17330050286805341, 11638888382251264, 16357706629708207, 16357706629708207, 11638888382251264,
    7924812503187618, 10112439506781552, 4754887502147955, 13499721339662996, 9002815015607054, 4754887502147955,
    9002815015607054, 9964340866974576, 14204036147538904, 9964340866974576, 13499721339662996, 14204036147538904,
    7924812503187618, 9964340866974576, 9964340866974576, 10112439506781552, 22999999826557761, 23000000171982640,
    27199512502091837, 30049937119743908, 28199512825033780, 28755029683390549, 32043023732759750, 34043023468427446,
    27755033125885038, 21953091291992413, 30139850435817238, 34437237438398852, 31139852426620681, 21953091291992413,
    25737740021921767, 33207416746371745, 30207416903614879, 22737712149631203, 22526640359215455, 28024833158990942,
    19534319982740128
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10053925881531105, 4754887502413606, 0, 6686500527235738, 9079484783826816, 11706064267418403,
    10215532999745656, 4087462841250340
  ]

abbrev PositiveTerm := Fin 43
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 327865512351 / 1000000000000
noncomputable def negativeCeiling : ℝ := 63257487269 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 246736924080067356040831696896, coefficient := 246736924080067356040831696896 }, { argument := 6374037205401740031054818836480, coefficient := 6374037205401740031054818836480 }, { argument := 246736924080067356040831696896, coefficient := 246736924080067356040831696896 }, { argument := 6497405667441773709075234684928, coefficient := 6497405667441773709075234684928 }, { argument := 6497405667441773709075234684928, coefficient := 6497405667441773709075234684928 }, { argument := 246736924080067356040831696896, coefficient := 246736924080067356040831696896 }, { argument := 168439073505325981723874438414336, coefficient := (-168439073505325981723874438414336) }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 85649976468057247769583157248, coefficient := 85649976468057247769583157248 }, { argument := 66848762121410534844552708096, coefficient := 66848762121410534844552708096 }, { argument := 896191217190159982759784742912, coefficient := 896191217190159982759784742912 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 66848762121410534844552708096, coefficient := 66848762121410534844552708096 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 2920455295179122741021396434944, coefficient := 2920455295179122741021396434944 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 896191217190159982759784742912, coefficient := 896191217190159982759784742912 }, { argument := 2920455295179122741021396434944, coefficient := 2920455295179122741021396434944 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 85649976468057247769583157248, coefficient := 85649976468057247769583157248 }, { argument := 8556641551540548460102746636288, coefficient := (-8556641551540548460102746636288) }, { argument := 79228153069531371854253522944, coefficient := 79228153069531371854253522944 }, { argument := 79228171958997303332834377728, coefficient := 79228171958997303332834377728 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1455656198494751273418741514240, coefficient := 1455656198494751273418741514240 }, { argument := 5249188016136436907292024111104, coefficient := 5249188016136436907292024111104 }, { argument := 1455656524338038591424261259264, coefficient := 1455656524338038591424261259264 }, { argument := 8160500738969226772135026884608, coefficient := (-8160500738969226772135026884608) }, { argument := 2139371217936764830336252116992, coefficient := 2139371217936764830336252116992 }, { argument := 83585505727375416427964778151936, coefficient := 83585505727375416427964778151936 }, { argument := 83585490412740912481705350135808, coefficient := 83585490412740912481705350135808 }, { argument := 2139376322814932812422728122368, coefficient := 2139376322814932812422728122368 }, { argument := 171449743680868026552429108527104, coefficient := (-171449743680868026552429108527104) }, { argument := 306774069228722988714825875456, coefficient := 306774069228722988714825875456 }, { argument := 44693948147726907524567663640576, coefficient := 44693948147726907524567663640576 }, { argument := 439401075812296776495929206243328, coefficient := 439401075812296776495929206243328 }, { argument := 44694009821833173802134154510336, coefficient := 44694009821833173802134154510336 }, { argument := 306774069228722988714825875456, coefficient := 306774069228722988714825875456 }, { argument := 529402581920314303800060676145152, coefficient := (-529402581920314303800060676145152) }, { argument := 264235676694173240728408293376, coefficient := 264235676694173240728408293376 }, { argument := 46836906938035975458633470181376, coefficient := 46836906938035975458633470181376 }, { argument := 46836912042914143440719946186752, coefficient := 46836912042914143440719946186752 }, { argument := 264230571816005258641932288000, coefficient := 264230571816005258641932288000 }, { argument := 94202285229460297398723756949504, coefficient := (-94202285229460297398723756949504) }, { argument := 28533440261496624483387047936, coefficient := 28533440261496624483387047936 }, { argument := 1289659590622794426934976577536, coefficient := 1289659590622794426934976577536 }, { argument := 28685731858202687671883530240, coefficient := 28685731858202687671883530240 }, { argument := 1346878762742493739090247155712, coefficient := (-1346878762742493739090247155712) }] }

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

end TermShard8


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
