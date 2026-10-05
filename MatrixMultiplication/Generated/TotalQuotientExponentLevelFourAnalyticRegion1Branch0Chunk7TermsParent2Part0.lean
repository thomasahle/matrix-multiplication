import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    105, 129, 209, 517, 1151, 2067,
    3669, 4587, 7037, 13793, 28275, 31857,
    31925, 72489, 117305
  ]
def positiveCoefficients : Array ℕ := #[
    812405578421266517684199666745344, 263195955872386129485753003016192, 831341109262175694369056670875648, 3010670175542044828554670112768, 25432240167078852367527608057856, 3010670175542044828554670112768,
    937110706218718585056437844574208, 25194555679536059354746976206848, 153702635277672814931475263651840, 4371176182236992033711006827937792, 154970285877901044332971966857216, 452313579793935103321542412468224,
    452313579793935103321542412468224, 1229858766708925312464582741065728, 933624667068090954202321910759424
  ]
def positiveScales : Array ℕ := #[
    6, 7, 7, 9, 10, 11,
    11, 12, 12, 13, 14, 14,
    14, 16, 16
  ]
def negativeArguments : Array ℕ := #[
    3, 9, 15, 29, 51, 103,
    143, 171, 239, 327, 691, 769,
    1167, 1661, 1923, 3073, 3307, 6593,
    6619, 10493, 7213263289911
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 713053462628379038341895553024, 2376844875427930127806318510080, 2297616712913665790212774559744, 16162545152909924869082965868544, 16321001477938453544270053769216,
    90637017916318402207014279184384, 54192063159756806913984062029824, 151484246727273413478856033042432, 829043492549262028578843896315904, 54746660297356657277138869682176, 243705827893877102437741191233536,
    92459265654146481971665790042112, 263195955872386129485753003016192, 152355756514930321192385016496128, 243468143406334309424960559382528, 262007533434672164421849843761152, 522351275456544777754235264565248,
    524411207681915650531667407273984, 831341109262175694369056670875648, 2185588091118496016855503413968896
  ]
def negativeScales : Array ℕ := #[
    1, 3, 3, 4, 5, 6,
    7, 7, 7, 8, 9, 9,
    10, 10, 10, 11, 11, 12,
    12, 13, 42
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6714245517659862, 7011227255423254, 7707359132075544, 9014020470314934, 10168672118132230, 11013322673425447,
    11841171189158040, 12163335192081960, 12780744797650887, 13751648659041397, 14787239403733748, 14959322792273422,
    14962398998685546, 16145474466408390, 16839904982356594
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 3169925001442313, 3906890600547867, 4857980997143165, 5672425342008812, 6686500527235738,
    7159871336778390, 7417852514885912, 7900866812416730, 8353146825498084, 9432541900388283, 9586839787965739,
    10188588845707349, 10697836358031166, 10909143052480768, 11585432051596722, 11691307330250036, 12686719366074642,
    12692397555528956, 13357139590005465, 42713789223051069
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 21
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
noncomputable def positiveFloor : ℝ := 83602818547 / 50000000000
noncomputable def negativeCeiling : ℝ := 106299016211 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-475368975085586025561263702016) }, { argument := 9, coefficient := (-713053462628379038341895553024) }, { argument := 15, coefficient := (-2376844875427930127806318510080) }, { argument := 29, coefficient := (-2297616712913665790212774559744) }, { argument := 51, coefficient := (-16162545152909924869082965868544) }, { argument := 103, coefficient := (-16321001477938453544270053769216) }, { argument := 105, coefficient := 812405578421266517684199666745344 }, { argument := 129, coefficient := 263195955872386129485753003016192 }, { argument := 143, coefficient := (-90637017916318402207014279184384) }, { argument := 171, coefficient := (-54192063159756806913984062029824) }, { argument := 209, coefficient := 831341109262175694369056670875648 }, { argument := 239, coefficient := (-151484246727273413478856033042432) }, { argument := 327, coefficient := (-829043492549262028578843896315904) }, { argument := 517, coefficient := 3010670175542044828554670112768 }, { argument := 691, coefficient := (-54746660297356657277138869682176) }, { argument := 769, coefficient := (-243705827893877102437741191233536) }, { argument := 1151, coefficient := 25432240167078852367527608057856 }, { argument := 1167, coefficient := (-92459265654146481971665790042112) }, { argument := 1661, coefficient := (-263195955872386129485753003016192) }, { argument := 1923, coefficient := (-152355756514930321192385016496128) }, { argument := 2067, coefficient := 3010670175542044828554670112768 }, { argument := 3073, coefficient := (-243468143406334309424960559382528) }, { argument := 3307, coefficient := (-262007533434672164421849843761152) }, { argument := 3669, coefficient := 937110706218718585056437844574208 }, { argument := 4587, coefficient := 25194555679536059354746976206848 }, { argument := 6593, coefficient := (-522351275456544777754235264565248) }, { argument := 6619, coefficient := (-524411207681915650531667407273984) }, { argument := 7037, coefficient := 153702635277672814931475263651840 }, { argument := 10493, coefficient := (-831341109262175694369056670875648) }, { argument := 13793, coefficient := 4371176182236992033711006827937792 }, { argument := 28275, coefficient := 154970285877901044332971966857216 }, { argument := 31857, coefficient := 452313579793935103321542412468224 }, { argument := 31925, coefficient := 452313579793935103321542412468224 }, { argument := 72489, coefficient := 1229858766708925312464582741065728 }, { argument := 117305, coefficient := 933624667068090954202321910759424 }, { argument := 7213263289911, coefficient := (-2185588091118496016855503413968896) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7
