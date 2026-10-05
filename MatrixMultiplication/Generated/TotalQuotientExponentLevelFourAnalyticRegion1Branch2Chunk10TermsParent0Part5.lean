import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
parent chunk 10, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

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
def constantNumerator : ℤ := (-54850527322417710280439526735216640)
def positiveArguments : Array ℕ := #[
    17634601509, 24021, 765, 23409, 13311, 24021,
    375003, 459, 13669660899, 23409, 765, 459,
    765, 11781, 13311, 102377097, 600589287, 43466251289,
    10185, 9021, 422241, 114945, 21733127889, 422241,
    10185, 10185, 4365, 10185, 114945, 4365,
    300292399, 9021, 289886305, 48597, 1522894751, 78279,
    2425, 78279, 52283, 290283617, 48597, 291,
    2675, 2445, 2675, 2445
  ]
def positiveCoefficients : Array ℕ := #[
    1332432817677825090171809745076224, 929267427614816236979745718272, 29594504064166122196807188480, 905591824363483339222299967488, 514944370716490526224445079552, 929267427614816236979745718272,
    14507225892254233100874883792896, 568214478031989546178698018816, 129106296923262684983325420945408, 905591824363483339222299967488, 29594504064166122196807188480, 568214478031989546178698018816,
    29594504064166122196807188480, 911510725176316563661661405184, 514944370716490526224445079552, 966924342972589012796282241024, 2836202718899377932836643274752, 205263568223163112688786440454144,
    394013103128799940620236881920, 348983034199794233120781238272, 16334657503996820395427534733312, 4446719306739313615571244810240, 205263589421866254290623804735488, 16334657503996820395427534733312,
    394013103128799940620236881920, 394013103128799940620236881920, 337725516967542806245917327360, 394013103128799940620236881920, 4446719306739313615571244810240, 337725516967542806245917327360,
    2836181520196236330999278993408, 348983034199794233120781238272, 1368949370574927247659268833280, 940002688892994144051136561152, 14383334258121028226339823419392, 1514136067737816914669196017664,
    46906321801047611978599628800, 1514136067737816914669196017664, 1011300298030586514258607996928, 1370825623446969152138412818432, 940002688892994144051136561152, 45030068929005707499455643648,
    206968100318024514709697331200, 189172712253297173258022420480, 206968100318024514709697331200, 189172712253297173258022420480
  ]
def positiveScales : Array ℕ := #[
    34, 14, 9, 14, 13, 14,
    18, 8, 33, 14, 9, 8,
    9, 13, 13, 26, 29, 35,
    13, 13, 18, 16, 34, 18,
    13, 13, 12, 13, 16, 12,
    28, 13, 28, 15, 30, 16,
    11, 16, 15, 28, 15, 8,
    11, 11, 11, 11
  ]
def negativeArguments : Array ℕ := #[
    10191, 5815, 73, 5
  ]
def negativeCoefficients : Array ℕ := #[
    1614828408365735728831612795748352, 460711765020447123106458071203840, 23134623454165186577314833498112, 792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    13, 12, 6, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    34037689924270051, 14552008591584190, 9579315937579817, 14514775685385275, 13700331338536850, 14552008591584190,
    18516542611559461, 8842350343321225, 33670258403563825, 14514775685385275, 9579315937579817, 8842350343321225,
    9579315937579817, 13524174383387515, 13700331338536850, 26609317762129723, 29161803500178082, 35339176625810587,
    13314158359853249, 13139071653295158, 18687707146971670, 16810584185923169, 34339176774805670, 18687707146971670,
    13314158359853249, 13314158359853249, 12091765938516802, 13314158359853249, 16810584185923169, 12091765938516802,
    28161792716965025, 13139071653295158, 28110911937357535, 15568579635382191, 30504169092950492, 16256337705464907,
    11243769031961852, 16256337705464907, 15674054304937220, 28112887910671408, 15568579635382191, 8184875342908283,
    11385323176175871, 11255618749839595, 11385323176175871, 11255618749839595
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    13315008003600358, 12505563476360907, 6189824558880018, 2321928094887363
  ]

abbrev PositiveTerm := Fin 46
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
noncomputable def positiveFloor : ℝ := 6352519913 / 8000000000
noncomputable def negativeCeiling : ℝ := 2639289801 / 8000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1332432817677825090171809745076224, coefficient := 1332432817677825090171809745076224 }, { argument := 929267427614816236979745718272, coefficient := 929267427614816236979745718272 }, { argument := 29594504064166122196807188480, coefficient := 29594504064166122196807188480 }, { argument := 905591824363483339222299967488, coefficient := 905591824363483339222299967488 }, { argument := 514944370716490526224445079552, coefficient := 514944370716490526224445079552 }, { argument := 929267427614816236979745718272, coefficient := 929267427614816236979745718272 }, { argument := 14507225892254233100874883792896, coefficient := 14507225892254233100874883792896 }, { argument := 568214478031989546178698018816, coefficient := 568214478031989546178698018816 }, { argument := 129106296923262684983325420945408, coefficient := 129106296923262684983325420945408 }, { argument := 905591824363483339222299967488, coefficient := 905591824363483339222299967488 }, { argument := 29594504064166122196807188480, coefficient := 29594504064166122196807188480 }, { argument := 568214478031989546178698018816, coefficient := 568214478031989546178698018816 }, { argument := 29594504064166122196807188480, coefficient := 29594504064166122196807188480 }, { argument := 911510725176316563661661405184, coefficient := 911510725176316563661661405184 }, { argument := 514944370716490526224445079552, coefficient := 514944370716490526224445079552 }, { argument := 966924342972589012796282241024, coefficient := 966924342972589012796282241024 }, { argument := 1614828408365735728831612795748352, coefficient := (-1614828408365735728831612795748352) }, { argument := 2836202718899377932836643274752, coefficient := 2836202718899377932836643274752 }, { argument := 205263568223163112688786440454144, coefficient := 205263568223163112688786440454144 }, { argument := 394013103128799940620236881920, coefficient := 394013103128799940620236881920 }, { argument := 348983034199794233120781238272, coefficient := 348983034199794233120781238272 }, { argument := 16334657503996820395427534733312, coefficient := 16334657503996820395427534733312 }, { argument := 4446719306739313615571244810240, coefficient := 4446719306739313615571244810240 }, { argument := 205263589421866254290623804735488, coefficient := 205263589421866254290623804735488 }, { argument := 16334657503996820395427534733312, coefficient := 16334657503996820395427534733312 }, { argument := 394013103128799940620236881920, coefficient := 394013103128799940620236881920 }, { argument := 394013103128799940620236881920, coefficient := 394013103128799940620236881920 }, { argument := 337725516967542806245917327360, coefficient := 337725516967542806245917327360 }, { argument := 394013103128799940620236881920, coefficient := 394013103128799940620236881920 }, { argument := 4446719306739313615571244810240, coefficient := 4446719306739313615571244810240 }, { argument := 337725516967542806245917327360, coefficient := 337725516967542806245917327360 }, { argument := 2836181520196236330999278993408, coefficient := 2836181520196236330999278993408 }, { argument := 348983034199794233120781238272, coefficient := 348983034199794233120781238272 }, { argument := 460711765020447123106458071203840, coefficient := (-460711765020447123106458071203840) }, { argument := 1368949370574927247659268833280, coefficient := 1368949370574927247659268833280 }, { argument := 940002688892994144051136561152, coefficient := 940002688892994144051136561152 }, { argument := 14383334258121028226339823419392, coefficient := 14383334258121028226339823419392 }, { argument := 1514136067737816914669196017664, coefficient := 1514136067737816914669196017664 }, { argument := 46906321801047611978599628800, coefficient := 46906321801047611978599628800 }, { argument := 1514136067737816914669196017664, coefficient := 1514136067737816914669196017664 }, { argument := 1011300298030586514258607996928, coefficient := 1011300298030586514258607996928 }, { argument := 1370825623446969152138412818432, coefficient := 1370825623446969152138412818432 }, { argument := 940002688892994144051136561152, coefficient := 940002688892994144051136561152 }, { argument := 45030068929005707499455643648, coefficient := 45030068929005707499455643648 }, { argument := 23134623454165186577314833498112, coefficient := (-23134623454165186577314833498112) }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
