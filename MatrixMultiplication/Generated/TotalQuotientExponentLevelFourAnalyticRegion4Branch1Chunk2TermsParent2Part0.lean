import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 2, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2

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
def constantNumerator : ℤ := 466814323978246214250338975744
def positiveArguments : Array ℕ := #[
    1, 32119, 1285123, 28285477, 1285123, 64225,
    300969, 1029763, 16480859, 74099
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 606710756253160538474807296, 24275287126259548263842578432, 267148777073560487380316585984, 24275287126259548263842578432, 606587974724605927699251200,
    2842571835965588500641742848, 155613384847977422854119489536, 155657312301001076293897289728, 2799381072113262725517279232
  ]
def positiveScales : Array ℕ := #[
    0, 14, 20, 24, 20, 15,
    18, 19, 23, 16
  ]
def negativeArguments : Array ℕ := #[
    9786678695, 16533725803, 529223456565, 2411360113, 48381964323, 10586839883543,
    5294911277621, 190595861491, 9786678695, 48381964323, 33247962331, 193527838109,
    9784674439, 33247962331, 233019489500217, 116542650604909, 4191027403629, 16533725803,
    10586839883543, 233019489500217, 10586839902765, 528972178399, 193527838109, 10586839902765,
    10589822575289, 190595841405, 529223456565, 5294911277621, 116542650604909, 10589822575289,
    529116381099, 9784674439, 528972178399, 529116381099, 9643463663, 2411360113,
    190595861491, 4191027403629, 190595841405, 9643463663, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2754705157749798254673920, 148922562730873509512216576, 148963160111366242188656640, 2714950126590719281856512, 108946498248257715887407104, 5959861019319420008494268416,
    5961540114213443124020117504, 107295931348653283519496192, 2754705157749798254673920, 108946498248257715887407104, 1197884086117759100710289408, 108946487449188759406379008,
    2754141009838876062121984, 1197884086117759100710289408, 65589155380202530400058212352, 65607679729629760330932420608, 1179669340830193858457370624, 148922562730873509512216576,
    5959861019319420008494268416, 65589155380202530400058212352, 5959861030140444013158727680, 148892431595443495836319744, 108946487449188759406379008, 5959861030140444013158727680,
    5961540125498900840257159168, 107295920041240519099023360, 148963160111366242188656640, 5961540114213443124020117504, 65607679729629760330932420608, 5961540125498900840257159168,
    148933021047067609550290944, 2754141009838876062121984, 148892431595443495836319744, 148933021047067609550290944, 2714393709952982400892928, 2714950126590719281856512,
    107295931348653283519496192, 1179669340830193858457370624, 107295920041240519099023360, 2714393709952982400892928, 316912650057057350374175801344, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    33, 33, 38, 31, 35, 43,
    42, 37, 33, 35, 34, 37,
    33, 34, 47, 46, 41, 33,
    43, 47, 43, 38, 37, 43,
    43, 37, 38, 42, 46, 43,
    38, 33, 38, 38, 33, 31,
    37, 41, 37, 33, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 14971139355004630, 20293475016679324, 24753558164671944, 20293475016679324, 15970847363764913,
    18199255370559777, 19973880907651264, 23974288102537513, 16177166452380480
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33188172189481365, 33944692824703044, 38945086060396419, 31167199973381172, 35493750293254125, 43267337250183723,
    42267743649039977, 37471725837346656, 33188172189481365, 35493750293254125, 34952546884578111, 37493750150250318,
    33187876703504265, 34952546884578111, 47727443953951435, 46727851356878376, 41930441100877911, 33944692824703044,
    43267337250183723, 47727443953951435, 43267337252803153, 38944400898187194, 37493750150250318, 43267337252803153,
    43267743651771062, 37471725685307814, 38945086060396419, 42267743649039977, 46727851356878376, 43267743651771062,
    38944794136641996, 33187876703504265, 38944400898187194, 38944794136641996, 33166904269314195, 31167199973381172,
    37471725837346656, 41930441100877911, 37471725685307814, 33166904269314195, 0, 0
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
noncomputable def positiveFloor : ℝ := 1368643 / 7812500000
noncomputable def negativeCeiling : ℝ := 4424767 / 25000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2754705157749798254673920, coefficient := (-2754705157749798254673920) }, { argument := 148922562730873509512216576, coefficient := (-148922562730873509512216576) }, { argument := 148963160111366242188656640, coefficient := (-148963160111366242188656640) }, { argument := 2714950126590719281856512, coefficient := (-2714950126590719281856512) }, { argument := 108946498248257715887407104, coefficient := (-108946498248257715887407104) }, { argument := 5959861019319420008494268416, coefficient := (-5959861019319420008494268416) }, { argument := 5961540114213443124020117504, coefficient := (-5961540114213443124020117504) }, { argument := 107295931348653283519496192, coefficient := (-107295931348653283519496192) }, { argument := 2754705157749798254673920, coefficient := (-2754705157749798254673920) }, { argument := 108946498248257715887407104, coefficient := (-108946498248257715887407104) }, { argument := 1197884086117759100710289408, coefficient := (-1197884086117759100710289408) }, { argument := 108946487449188759406379008, coefficient := (-108946487449188759406379008) }, { argument := 2754141009838876062121984, coefficient := (-2754141009838876062121984) }, { argument := 1197884086117759100710289408, coefficient := (-1197884086117759100710289408) }, { argument := 65589155380202530400058212352, coefficient := (-65589155380202530400058212352) }, { argument := 65607679729629760330932420608, coefficient := (-65607679729629760330932420608) }, { argument := 1179669340830193858457370624, coefficient := (-1179669340830193858457370624) }, { argument := 148922562730873509512216576, coefficient := (-148922562730873509512216576) }, { argument := 5959861019319420008494268416, coefficient := (-5959861019319420008494268416) }, { argument := 65589155380202530400058212352, coefficient := (-65589155380202530400058212352) }, { argument := 5959861030140444013158727680, coefficient := (-5959861030140444013158727680) }, { argument := 148892431595443495836319744, coefficient := (-148892431595443495836319744) }, { argument := 108946487449188759406379008, coefficient := (-108946487449188759406379008) }, { argument := 5959861030140444013158727680, coefficient := (-5959861030140444013158727680) }, { argument := 5961540125498900840257159168, coefficient := (-5961540125498900840257159168) }, { argument := 107295920041240519099023360, coefficient := (-107295920041240519099023360) }, { argument := 148963160111366242188656640, coefficient := (-148963160111366242188656640) }, { argument := 5961540114213443124020117504, coefficient := (-5961540114213443124020117504) }, { argument := 65607679729629760330932420608, coefficient := (-65607679729629760330932420608) }, { argument := 5961540125498900840257159168, coefficient := (-5961540125498900840257159168) }, { argument := 148933021047067609550290944, coefficient := (-148933021047067609550290944) }, { argument := 2754141009838876062121984, coefficient := (-2754141009838876062121984) }, { argument := 148892431595443495836319744, coefficient := (-148892431595443495836319744) }, { argument := 148933021047067609550290944, coefficient := (-148933021047067609550290944) }, { argument := 2714393709952982400892928, coefficient := (-2714393709952982400892928) }, { argument := 2714950126590719281856512, coefficient := (-2714950126590719281856512) }, { argument := 107295931348653283519496192, coefficient := (-107295931348653283519496192) }, { argument := 1179669340830193858457370624, coefficient := (-1179669340830193858457370624) }, { argument := 107295920041240519099023360, coefficient := (-107295920041240519099023360) }, { argument := 2714393709952982400892928, coefficient := (-2714393709952982400892928) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 606710756253160538474807296, coefficient := 606710756253160538474807296 }, { argument := 24275287126259548263842578432, coefficient := 24275287126259548263842578432 }, { argument := 267148777073560487380316585984, coefficient := 267148777073560487380316585984 }, { argument := 24275287126259548263842578432, coefficient := 24275287126259548263842578432 }, { argument := 606587974724605927699251200, coefficient := 606587974724605927699251200 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 2842571835965588500641742848, coefficient := 2842571835965588500641742848 }, { argument := 155613384847977422854119489536, coefficient := 155613384847977422854119489536 }, { argument := 155657312301001076293897289728, coefficient := 155657312301001076293897289728 }, { argument := 2799381072113262725517279232, coefficient := 2799381072113262725517279232 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2
