import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    53, 425, 489, 1955, 2425, 4835,
    16995, 23705, 23835, 27027, 33825, 57611,
    65547, 131683
  ]
def positiveCoefficients : Array ℕ := #[
    804245077682297290912064639860736, 814861651459208712149599529205760, 2772985687999251815774038261760, 2693757525484987478180494311424, 34464250693704986853191618396160, 34226566206162193840410986545152,
    507456380903863082286649001902080, 106007281444085683700161805549568, 106878791231742591413690789003264, 4282599096546044504281424691462144, 506267958466149117222745842647040, 1058409023028057285912153632538624,
    961354523948083472360062293377024, 961433752110597736697655837327360
  ]
def positiveScales : Array ℕ := #[
    5, 8, 8, 10, 11, 12,
    14, 14, 14, 14, 15, 15,
    16, 17
  ]
def negativeArguments : Array ℕ := #[
    3, 13, 27, 105, 157, 203,
    287, 303, 317, 321, 601, 635,
    2283, 3237, 3447, 3453, 6069, 6083,
    10257, 10285, 7172436928305
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 2059932225370872777432142708736, 2139160387885137115025686659072, 8318957063997755447322114785280, 49755286058958004008745600811008, 257333071846330568503830750691328,
    181907861132750919114776909971456, 48012266483644188581687633903616, 25115327517021795017153432256512, 25432240167078852367527608057856, 47616125671072866893719914151936, 50309883196557854371900408463360,
    180877895020065482726060838617088, 256461562058673660790301767237632, 273099476186669171684945996808192, 273574845161754757710507260510208, 480835718299070264855218234589184, 481944912574269965581527849893888,
    812643262908809310696980298596352, 814861651459208712149599529205760, 2141299548273022252140712345731072
  ]
def negativeScales : Array ℕ := #[
    1, 3, 4, 6, 7, 7,
    8, 8, 8, 8, 9, 9,
    11, 11, 11, 11, 12, 12,
    13, 13, 42
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5727920454554652, 8731319031015838, 8933690654464738, 10932952891713365, 11243769031961852, 12239300174364203,
    14052822741429034, 14532903772613708, 14540794004956974, 14722113760991968, 15045802313751261, 15814056679537357,
    16000242131252519, 17006709583138735
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 3700439718214233, 4754887502413606, 6714245517766967, 7294620748891628, 7665335917216502,
    8164906926675688, 8243173983472952, 8308339030139408, 8326429487122304, 9231221180711186, 9310612781659529,
    11156715144224702, 11660441650236901, 11751125583597746, 11753634619096809, 12567243105281663, 12570567288874455,
    13324321208154552, 13328254173412297, 42705600515266591
  ]

abbrev PositiveTerm := Fin 14
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
noncomputable def positiveFloor : ℝ := 854297921933 / 500000000000
noncomputable def negativeCeiling : ℝ := 428181456003 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-475368975085586025561263702016) }, { argument := 13, coefficient := (-2059932225370872777432142708736) }, { argument := 27, coefficient := (-2139160387885137115025686659072) }, { argument := 53, coefficient := 804245077682297290912064639860736 }, { argument := 105, coefficient := (-8318957063997755447322114785280) }, { argument := 157, coefficient := (-49755286058958004008745600811008) }, { argument := 203, coefficient := (-257333071846330568503830750691328) }, { argument := 287, coefficient := (-181907861132750919114776909971456) }, { argument := 303, coefficient := (-48012266483644188581687633903616) }, { argument := 317, coefficient := (-25115327517021795017153432256512) }, { argument := 321, coefficient := (-25432240167078852367527608057856) }, { argument := 425, coefficient := 814861651459208712149599529205760 }, { argument := 489, coefficient := 2772985687999251815774038261760 }, { argument := 601, coefficient := (-47616125671072866893719914151936) }, { argument := 635, coefficient := (-50309883196557854371900408463360) }, { argument := 1955, coefficient := 2693757525484987478180494311424 }, { argument := 2283, coefficient := (-180877895020065482726060838617088) }, { argument := 2425, coefficient := 34464250693704986853191618396160 }, { argument := 3237, coefficient := (-256461562058673660790301767237632) }, { argument := 3447, coefficient := (-273099476186669171684945996808192) }, { argument := 3453, coefficient := (-273574845161754757710507260510208) }, { argument := 4835, coefficient := 34226566206162193840410986545152 }, { argument := 6069, coefficient := (-480835718299070264855218234589184) }, { argument := 6083, coefficient := (-481944912574269965581527849893888) }, { argument := 10257, coefficient := (-812643262908809310696980298596352) }, { argument := 10285, coefficient := (-814861651459208712149599529205760) }, { argument := 16995, coefficient := 507456380903863082286649001902080 }, { argument := 23705, coefficient := 106007281444085683700161805549568 }, { argument := 23835, coefficient := 106878791231742591413690789003264 }, { argument := 27027, coefficient := 4282599096546044504281424691462144 }, { argument := 33825, coefficient := 506267958466149117222745842647040 }, { argument := 57611, coefficient := 1058409023028057285912153632538624 }, { argument := 65547, coefficient := 961354523948083472360062293377024 }, { argument := 131683, coefficient := 961433752110597736697655837327360 }, { argument := 7172436928305, coefficient := (-2141299548273022252140712345731072) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7
