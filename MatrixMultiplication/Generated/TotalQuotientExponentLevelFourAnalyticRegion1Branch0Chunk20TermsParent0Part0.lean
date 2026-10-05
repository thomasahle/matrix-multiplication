import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 20, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    129, 175, 383, 649, 967, 1859,
    3855, 5193, 7105, 33245, 36777, 36947,
    38527
  ]
def positiveCoefficients : Array ℕ := #[
    136430895849563189336082682478592, 158456325028528675187087900672, 290846584589864383305899841683456, 4516005263313067242832005169152, 115039291970711818185825815887872, 9348923176683191836038186139648,
    114643151158140496497858096136192, 4516005263313067242832005169152, 1125832189327696237204259534274560, 323726272033284083407220581072896, 109255636107170521541497107513344, 109651776919741843229464827265024,
    334976671110309619345503822020608
  ]
def positiveScales : Array ℕ := #[
    7, 7, 8, 9, 9, 10,
    11, 12, 12, 15, 15, 15,
    15
  ]
def negativeArguments : Array ℕ := #[
    3, 9, 25, 47, 51, 59,
    195, 277, 363, 423, 561, 767,
    843, 1447, 2043, 2539, 2744029065539
  ]
def negativeCoefficients : Array ℕ := #[
    3802951800684688204490109616128, 713053462628379038341895553024, 3961408125713216879677197516800, 3723723638170423866896565665792, 4040636288227481217270741467136, 9348923176683191836038186139648,
    61797966761126183322964281262080, 43892402032902443026823348486144, 115039291970711818185825815887872, 67027025487067629604138181984256, 44446999170502293389978156138496, 60768000648440746934248209907712,
    66789340999524836591357550133248, 114643151158140496497858096136192, 323726272033284083407220581072896, 201160304623717153150008089903104, 562916094663848118602129767137280
  ]
def negativeScales : Array ℕ := #[
    1, 3, 4, 5, 5, 5,
    7, 8, 8, 8, 9, 9,
    9, 10, 10, 11, 41
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7011227255423254, 7451211111832325, 8581200581924749, 9342074667999138, 9917372079109592, 10860311054789169,
    11912515144465203, 12342352510087794, 12794618934094284, 15020849757227174, 15166516179537344, 15173169605603351,
    15233582230908271
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 3169925001442313, 4643856189792934, 5554588851679165, 5672425342008812, 5882643052550791,
    7607330313756529, 8113742166049189, 8503825737996059, 8724513853247462, 9131856960608793, 9583082767506450,
    9719388821055554, 10498849206531986, 10996473511112608, 11310044679647506, 41319432901677621
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 17
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
noncomputable def positiveFloor : ℝ := 407460585783 / 1000000000000
noncomputable def negativeCeiling : ℝ := 414676071997 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-3802951800684688204490109616128) }, { argument := 9, coefficient := (-713053462628379038341895553024) }, { argument := 25, coefficient := (-3961408125713216879677197516800) }, { argument := 47, coefficient := (-3723723638170423866896565665792) }, { argument := 51, coefficient := (-4040636288227481217270741467136) }, { argument := 59, coefficient := (-9348923176683191836038186139648) }, { argument := 129, coefficient := 136430895849563189336082682478592 }, { argument := 175, coefficient := 158456325028528675187087900672 }, { argument := 195, coefficient := (-61797966761126183322964281262080) }, { argument := 277, coefficient := (-43892402032902443026823348486144) }, { argument := 363, coefficient := (-115039291970711818185825815887872) }, { argument := 383, coefficient := 290846584589864383305899841683456 }, { argument := 423, coefficient := (-67027025487067629604138181984256) }, { argument := 561, coefficient := (-44446999170502293389978156138496) }, { argument := 649, coefficient := 4516005263313067242832005169152 }, { argument := 767, coefficient := (-60768000648440746934248209907712) }, { argument := 843, coefficient := (-66789340999524836591357550133248) }, { argument := 967, coefficient := 115039291970711818185825815887872 }, { argument := 1447, coefficient := (-114643151158140496497858096136192) }, { argument := 1859, coefficient := 9348923176683191836038186139648 }, { argument := 2043, coefficient := (-323726272033284083407220581072896) }, { argument := 2539, coefficient := (-201160304623717153150008089903104) }, { argument := 3855, coefficient := 114643151158140496497858096136192 }, { argument := 5193, coefficient := 4516005263313067242832005169152 }, { argument := 7105, coefficient := 1125832189327696237204259534274560 }, { argument := 33245, coefficient := 323726272033284083407220581072896 }, { argument := 36777, coefficient := 109255636107170521541497107513344 }, { argument := 36947, coefficient := 109651776919741843229464827265024 }, { argument := 38527, coefficient := 334976671110309619345503822020608 }, { argument := 2744029065539, coefficient := (-562916094663848118602129767137280) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20
