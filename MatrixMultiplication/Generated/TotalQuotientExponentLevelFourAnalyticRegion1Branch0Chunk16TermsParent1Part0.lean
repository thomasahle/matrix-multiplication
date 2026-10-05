import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 16, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk16

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
    49, 75, 185, 2053, 2097, 2101,
    4795, 6781, 16489, 17577, 27191, 35327,
    46001
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 5070602400912917605986812821504, 267474276648156403715804376334336, 89765508128661494493485295730688, 4040636288227481217270741467136, 4119864450741745554864285417472,
    4991374238398653268393268871168, 1074492340018452946443643054456832, 90240877103747080519046559432704, 130171871010936306666192710402048, 266285854210442438651901217079296, 130726468148536157029347518054400,
    348920827712820142761967557279744
  ]
def positiveScales : Array ℕ := #[
    5, 6, 7, 11, 11, 11,
    12, 12, 14, 14, 14, 15,
    15
  ]
def negativeArguments : Array ℕ := #[
    9, 17, 27, 43, 63, 273,
    535, 539, 825, 1061, 1065, 1139,
    1643, 3361, 10664291475
  ]
def negativeCoefficients : Array ℕ := #[
    713053462628379038341895553024, 43100120407759799650887908982784, 8556641551540548460102746636288, 6813621976226733033044779728896, 4991374238398653268393268871168, 43258576732788328326074996883456,
    42387066945131420612546013429760, 42703979595188477962920189231104, 130726468148536157029347518054400, 84061080427634462186750131306496, 84377993077691519537124307107840, 180481754207494161038093118865408,
    130171871010936306666192710402048, 266285854210442438651901217079296, 537246170009226473221821527228416
  ]
def negativeScales : Array ℕ := #[
    3, 4, 4, 5, 5, 8,
    9, 9, 9, 10, 10, 10,
    10, 11, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5614709844114682, 6228818690495880, 7531381460516264, 11003517912108601, 11034111146096592, 11036860446673045,
    12227315099905492, 12727282329203763, 14009216286585156, 14101401235329103, 14730841589693420, 15108483619044364,
    15489377603313862
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 4087462841250340, 4754887502413606, 5426264754702117, 5977279939904027, 8092757140919853,
    9063395081288510, 9074141462752506, 9688250309187948, 10051208940914765, 10056637715113201, 10153552031708112,
    10682116764997329, 11714674827409848, 33312069066501514
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 15
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
noncomputable def positiveFloor : ℝ := 376316889507 / 1000000000000
noncomputable def negativeCeiling : ℝ := 17217174771 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9, coefficient := (-713053462628379038341895553024) }, { argument := 17, coefficient := (-43100120407759799650887908982784) }, { argument := 27, coefficient := (-8556641551540548460102746636288) }, { argument := 43, coefficient := (-6813621976226733033044779728896) }, { argument := 49, coefficient := 158456325028528675187087900672 }, { argument := 63, coefficient := (-4991374238398653268393268871168) }, { argument := 75, coefficient := 5070602400912917605986812821504 }, { argument := 185, coefficient := 267474276648156403715804376334336 }, { argument := 273, coefficient := (-43258576732788328326074996883456) }, { argument := 535, coefficient := (-42387066945131420612546013429760) }, { argument := 539, coefficient := (-42703979595188477962920189231104) }, { argument := 825, coefficient := (-130726468148536157029347518054400) }, { argument := 1061, coefficient := (-84061080427634462186750131306496) }, { argument := 1065, coefficient := (-84377993077691519537124307107840) }, { argument := 1139, coefficient := (-180481754207494161038093118865408) }, { argument := 1643, coefficient := (-130171871010936306666192710402048) }, { argument := 2053, coefficient := 89765508128661494493485295730688 }, { argument := 2097, coefficient := 4040636288227481217270741467136 }, { argument := 2101, coefficient := 4119864450741745554864285417472 }, { argument := 3361, coefficient := (-266285854210442438651901217079296) }, { argument := 4795, coefficient := 4991374238398653268393268871168 }, { argument := 6781, coefficient := 1074492340018452946443643054456832 }, { argument := 16489, coefficient := 90240877103747080519046559432704 }, { argument := 17577, coefficient := 130171871010936306666192710402048 }, { argument := 27191, coefficient := 266285854210442438651901217079296 }, { argument := 35327, coefficient := 130726468148536157029347518054400 }, { argument := 46001, coefficient := 348920827712820142761967557279744 }, { argument := 10664291475, coefficient := (-537246170009226473221821527228416) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk16
