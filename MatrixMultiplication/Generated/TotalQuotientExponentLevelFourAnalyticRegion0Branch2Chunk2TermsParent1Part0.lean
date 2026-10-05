import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 2, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 40359, 66303, 14579815, 528377, 2465,
    81777, 4112901, 8222481, 165379
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 381179977764272022359113728, 10019426077238594771317948416, 137702459364880192662646292480, 9980759340476858116308205568, 372500268168757614456340480,
    1544723855478523906561671168, 77690503319044186676221968384, 77659137360864966492712599552, 1561960493140998111591661568
  ]
def positiveScales : Array ℕ := #[
    0, 15, 16, 23, 19, 11,
    16, 21, 22, 17
  ]
def negativeArguments : Array ℕ := #[
    3300437943, 165992571459, 331851110679, 6674531061, 5422060431, 272697675003,
    545175157743, 10965123837, 3300437943, 5422060431, 1192293531255, 43209085929,
    201580305, 1192293531255, 59965335693315, 119882251821015, 2411195224885, 165992571459,
    272697675003, 59965335693315, 2173162291677, 10138300965, 43209085929, 2173162291677,
    4344569843337, 87382459883, 331851110679, 545175157743, 119882251821015, 4344569843337,
    20268415665, 201580305, 10138300965, 20268415665, 407659235, 6674531061,
    10965123837, 2411195224885, 87382459883, 407659235, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1857981386281780789641216, 93445510371127853693534208, 93407783649776851614695424, 1878713474949525081686016, 48837578673263821876887552, 2456242295056622843357822976,
    2455250637263026177104150528, 49382527626384543320113152, 1857981386281780789641216, 48837578673263821876887552, 671201587884533853255106560, 48649105822216035495837696,
    1815673972966461863362560, 671201587884533853255106560, 33757482935445017175816929280, 33743854039341194970755235840, 678691119769350331495874560, 93445510371127853693534208,
    2456242295056622843357822976, 33757482935445017175816929280, 2446763221753037585224040448, 91317696896287880018657280, 48649105822216035495837696, 2446763221753037585224040448,
    2445775390942200922996998144, 49191951720974514437226496, 93407783649776851614695424, 2455250637263026177104150528, 33743854039341194970755235840, 2445775390942200922996998144,
    91280829236284323885219840, 1815673972966461863362560, 91317696896287880018657280, 91280829236284323885219840, 1835933978840141460930560, 1878713474949525081686016,
    49382527626384543320113152, 678691119769350331495874560, 49191951720974514437226496, 1835933978840141460930560, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    31, 37, 38, 32, 32, 37,
    38, 33, 31, 32, 40, 35,
    27, 40, 45, 46, 41, 37,
    37, 45, 40, 33, 35, 40,
    41, 36, 38, 38, 46, 41,
    34, 27, 33, 34, 28, 32,
    33, 41, 36, 28, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15300602807885839, 16016786528729018, 23797469077920961, 19011208142558024, 11267371931265273,
    16319407517927179, 21971724914119468, 22971142337783268, 17335416525636905
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31620010325822766, 37272327722929176, 38271745146584168, 32636019333537614, 32336194046656200, 37988511463462386,
    38987928886932903, 33352203054365926, 31620010325822766, 32336194046656200, 40116876595886155, 35330615660485206,
    27586779449196360, 40116876595886155, 45769193993342459, 46768611416993260, 41132885603595881, 37272327722929176,
    37988511463462386, 45769193993342459, 40982933075589669, 33239096846308610, 35330615660485206, 40982933075589669,
    41982350499075062, 36346624668194931, 38271745146584168, 38987928886932903, 46768611416993260, 41982350499075062,
    34238514269963602, 27586779449196360, 33239096846308610, 34238514269963602, 28602788456908287, 32636019333537614,
    33352203054365926, 41132885603595881, 36346624668194931, 28602788456908287, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 43215607 / 500000000000
noncomputable def negativeCeiling : ℝ := 17286243 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1857981386281780789641216, coefficient := (-1857981386281780789641216) }, { argument := 93445510371127853693534208, coefficient := (-93445510371127853693534208) }, { argument := 93407783649776851614695424, coefficient := (-93407783649776851614695424) }, { argument := 1878713474949525081686016, coefficient := (-1878713474949525081686016) }, { argument := 48837578673263821876887552, coefficient := (-48837578673263821876887552) }, { argument := 2456242295056622843357822976, coefficient := (-2456242295056622843357822976) }, { argument := 2455250637263026177104150528, coefficient := (-2455250637263026177104150528) }, { argument := 49382527626384543320113152, coefficient := (-49382527626384543320113152) }, { argument := 1857981386281780789641216, coefficient := (-1857981386281780789641216) }, { argument := 48837578673263821876887552, coefficient := (-48837578673263821876887552) }, { argument := 671201587884533853255106560, coefficient := (-671201587884533853255106560) }, { argument := 48649105822216035495837696, coefficient := (-48649105822216035495837696) }, { argument := 1815673972966461863362560, coefficient := (-1815673972966461863362560) }, { argument := 671201587884533853255106560, coefficient := (-671201587884533853255106560) }, { argument := 33757482935445017175816929280, coefficient := (-33757482935445017175816929280) }, { argument := 33743854039341194970755235840, coefficient := (-33743854039341194970755235840) }, { argument := 678691119769350331495874560, coefficient := (-678691119769350331495874560) }, { argument := 93445510371127853693534208, coefficient := (-93445510371127853693534208) }, { argument := 2456242295056622843357822976, coefficient := (-2456242295056622843357822976) }, { argument := 33757482935445017175816929280, coefficient := (-33757482935445017175816929280) }, { argument := 2446763221753037585224040448, coefficient := (-2446763221753037585224040448) }, { argument := 91317696896287880018657280, coefficient := (-91317696896287880018657280) }, { argument := 48649105822216035495837696, coefficient := (-48649105822216035495837696) }, { argument := 2446763221753037585224040448, coefficient := (-2446763221753037585224040448) }, { argument := 2445775390942200922996998144, coefficient := (-2445775390942200922996998144) }, { argument := 49191951720974514437226496, coefficient := (-49191951720974514437226496) }, { argument := 93407783649776851614695424, coefficient := (-93407783649776851614695424) }, { argument := 2455250637263026177104150528, coefficient := (-2455250637263026177104150528) }, { argument := 33743854039341194970755235840, coefficient := (-33743854039341194970755235840) }, { argument := 2445775390942200922996998144, coefficient := (-2445775390942200922996998144) }, { argument := 91280829236284323885219840, coefficient := (-91280829236284323885219840) }, { argument := 1815673972966461863362560, coefficient := (-1815673972966461863362560) }, { argument := 91317696896287880018657280, coefficient := (-91317696896287880018657280) }, { argument := 91280829236284323885219840, coefficient := (-91280829236284323885219840) }, { argument := 1835933978840141460930560, coefficient := (-1835933978840141460930560) }, { argument := 1878713474949525081686016, coefficient := (-1878713474949525081686016) }, { argument := 49382527626384543320113152, coefficient := (-49382527626384543320113152) }, { argument := 678691119769350331495874560, coefficient := (-678691119769350331495874560) }, { argument := 49191951720974514437226496, coefficient := (-49191951720974514437226496) }, { argument := 1835933978840141460930560, coefficient := (-1835933978840141460930560) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 381179977764272022359113728, coefficient := 381179977764272022359113728 }, { argument := 10019426077238594771317948416, coefficient := 10019426077238594771317948416 }, { argument := 137702459364880192662646292480, coefficient := 137702459364880192662646292480 }, { argument := 9980759340476858116308205568, coefficient := 9980759340476858116308205568 }, { argument := 372500268168757614456340480, coefficient := 372500268168757614456340480 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1544723855478523906561671168, coefficient := 1544723855478523906561671168 }, { argument := 77690503319044186676221968384, coefficient := 77690503319044186676221968384 }, { argument := 77659137360864966492712599552, coefficient := 77659137360864966492712599552 }, { argument := 1561960493140998111591661568, coefficient := 1561960493140998111591661568 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2
