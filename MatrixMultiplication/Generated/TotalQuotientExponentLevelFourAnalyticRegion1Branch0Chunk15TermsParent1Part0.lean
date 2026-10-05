import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 15, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    95, 257, 461, 469, 1335, 1983,
    5407, 6105, 8897, 9111, 13595, 35783,
    36689, 48735, 66179
  ]
def positiveCoefficients : Array ℕ := #[
    92459265654146481971665790042112, 110998655682484336968555074420736, 899873469837014346387472187916288, 900824207787185518438594715320320, 64254039799068377788364143722496, 2287317051786811426325613846200320,
    65759374886839400202641478778880, 92855406466717803659633509793792, 1059042848328171400612901984141312, 968247374086824469730700617056256, 8616854955051389356673840038543360, 1060072814440856837001618055495680,
    971891869562480629260003638771712, 2002254123060488339664042712891392, 2236769484102710778940932805885952
  ]
def positiveScales : Array ℕ := #[
    6, 8, 8, 8, 10, 10,
    12, 12, 13, 13, 13, 15,
    15, 15, 16
  ]
def negativeArguments : Array ℕ := #[
    3, 7, 11, 97, 101, 103,
    127, 133, 187, 197, 239, 293,
    399, 487, 557, 647, 663, 1115,
    1167, 1439, 2883, 3159, 3345, 3987,
    6323, 6339, 13367, 5301152863493
  ]
def negativeCoefficients : Array ℕ := #[
    1188422437713965063903159255040, 1109194275199700726309615304704, 1743019575313815427057966907392, 30740527055534562986295052730368, 16004088827881396193895877967872, 16321001477938453544270053769216,
    10061976639311570874380081692672, 10537345614397156899941345394688, 29631332780334862259985437425664, 62431792061240298023712632864768, 37871061681818353369714008260608, 92855406466717803659633509793792,
    63224073686382941399648072368128, 38584115144446732408055903813632, 353040692163561888316831842697216, 51260621146729026423022935867392, 52528271746957255824519639072768, 353357604813618945667206018498560,
    92459265654146481971665790042112, 456037303432105527188438978134016, 456829585057248170564374417637376, 2002254123060488339664042712891392, 1060072814440856837001618055495680, 1263530735777487655941838919958528,
    500959671577693406603978397974528, 502227322177921636005475101179904, 1059042848328171400612901984141312, 4308427477525694678336920019271680
  ]
def negativeScales : Array ℕ := #[
    1, 2, 3, 6, 6, 6,
    6, 7, 7, 7, 7, 8,
    8, 8, 9, 9, 9, 10,
    10, 10, 11, 11, 11, 11,
    12, 12, 13, 42
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6569855608330797, 8005624549193878, 8848622940324922, 8873444112348880, 10382624026574915, 10953468961546680,
    12400612641081998, 12575775579874587, 13119103237062562, 13153393693888615, 13730788530903005, 15126986725678429,
    15163059962394235, 15572670623937839, 16014085871472781
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2807354922807594, 3459431618637364, 6599912842192769, 6658211482778016, 6686500527235738,
    6988684706517367, 7055282435501190, 7546894459888847, 7622051819466668, 7900866812416730, 8194756854422248,
    8640244936238936, 8927777969209522, 9121533517340032, 9337621901992509, 9372865060112590, 10122827994807668,
    10188588845707349, 10490850876740497, 11493355121495124, 11625252221758078, 11707790495615677, 11961087902552566,
    12626393504185545, 12630039552668812, 13706388092576406, 42269443281263107
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 28
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
noncomputable def positiveFloor : ℝ := 346516864403 / 100000000000
noncomputable def negativeCeiling : ℝ := 3395289286653 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-1188422437713965063903159255040) }, { argument := 7, coefficient := (-1109194275199700726309615304704) }, { argument := 11, coefficient := (-1743019575313815427057966907392) }, { argument := 95, coefficient := 92459265654146481971665790042112 }, { argument := 97, coefficient := (-30740527055534562986295052730368) }, { argument := 101, coefficient := (-16004088827881396193895877967872) }, { argument := 103, coefficient := (-16321001477938453544270053769216) }, { argument := 127, coefficient := (-10061976639311570874380081692672) }, { argument := 133, coefficient := (-10537345614397156899941345394688) }, { argument := 187, coefficient := (-29631332780334862259985437425664) }, { argument := 197, coefficient := (-62431792061240298023712632864768) }, { argument := 239, coefficient := (-37871061681818353369714008260608) }, { argument := 257, coefficient := 110998655682484336968555074420736 }, { argument := 293, coefficient := (-92855406466717803659633509793792) }, { argument := 399, coefficient := (-63224073686382941399648072368128) }, { argument := 461, coefficient := 899873469837014346387472187916288 }, { argument := 469, coefficient := 900824207787185518438594715320320 }, { argument := 487, coefficient := (-38584115144446732408055903813632) }, { argument := 557, coefficient := (-353040692163561888316831842697216) }, { argument := 647, coefficient := (-51260621146729026423022935867392) }, { argument := 663, coefficient := (-52528271746957255824519639072768) }, { argument := 1115, coefficient := (-353357604813618945667206018498560) }, { argument := 1167, coefficient := (-92459265654146481971665790042112) }, { argument := 1335, coefficient := 64254039799068377788364143722496 }, { argument := 1439, coefficient := (-456037303432105527188438978134016) }, { argument := 1983, coefficient := 2287317051786811426325613846200320 }, { argument := 2883, coefficient := (-456829585057248170564374417637376) }, { argument := 3159, coefficient := (-2002254123060488339664042712891392) }, { argument := 3345, coefficient := (-1060072814440856837001618055495680) }, { argument := 3987, coefficient := (-1263530735777487655941838919958528) }, { argument := 5407, coefficient := 65759374886839400202641478778880 }, { argument := 6105, coefficient := 92855406466717803659633509793792 }, { argument := 6323, coefficient := (-500959671577693406603978397974528) }, { argument := 6339, coefficient := (-502227322177921636005475101179904) }, { argument := 8897, coefficient := 1059042848328171400612901984141312 }, { argument := 9111, coefficient := 968247374086824469730700617056256 }, { argument := 13367, coefficient := (-1059042848328171400612901984141312) }, { argument := 13595, coefficient := 8616854955051389356673840038543360 }, { argument := 35783, coefficient := 1060072814440856837001618055495680 }, { argument := 36689, coefficient := 971891869562480629260003638771712 }, { argument := 48735, coefficient := 2002254123060488339664042712891392 }, { argument := 66179, coefficient := 2236769484102710778940932805885952 }, { argument := 5301152863493, coefficient := (-4308427477525694678336920019271680) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15
