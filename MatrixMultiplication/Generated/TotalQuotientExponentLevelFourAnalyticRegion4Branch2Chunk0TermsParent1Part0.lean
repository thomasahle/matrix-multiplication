import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 0, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0

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
def constantNumerator : ℤ := 10173114021045244719468378062848
def positiveArguments : Array ℕ := #[
    1, 84047, 8220507, 4110255, 168105, 39217
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 1587602943142980285102030848, 77640493457990597133408927744, 77640521792189494351280209920, 1587706835205603417296732160, 740788185434795505382064128
  ]
def positiveScales : Array ℕ := #[
    0, 16, 22, 21, 17, 15
  ]
def negativeArguments : Array ℕ := #[
    14569127215, 345233390281, 690282633585, 7378065895, 1537973089, 5958670197,
    8742763461, 47669714529, 769084587, 1424983785915, 33766743624861, 67515476118885,
    721637206995, 5958670197, 23086067481, 33872662953, 184689907317, 2979714951,
    14569127215, 1424983785915, 712492152975, 29140161225, 712492152975, 16883377973865,
    33757750379025, 360818735175, 8742763461, 33872662953, 49699122489, 270983310021,
    4371939063, 345233390281, 33766743624861, 16883377973865, 690511964415, 29140161225,
    690511964415, 1380655610775, 14757097425, 47669714529, 184689907317, 270983310021,
    1477530198369, 23837896107, 690282633585, 67515476118885, 33757750379025, 1380655610775,
    769084587, 2979714951, 4371939063, 23837896107, 384591321, 7378065895,
    721637206995, 360818735175, 14757097425, 1
  ]
def negativeCoefficients : Array ℕ := #[
    8201689487073419020206080, 388698241956341153838137344, 388594576424216328425963520, 8306963703859241266708480, 865801878815781335072768, 26835464878832879992307712,
    314991250121183903505973248, 26835663573707789904642048, 865912264857397953036288, 401097277953487040403210240, 19008986750804883871610437632, 19003917068172006718502338560,
    406245632064920936188477440, 26835464878832879992307712, 831763239239053801955524608, 9763130384203341098523820032, 831769397771932642660319232, 26838886285987791494971392,
    8201689487073419020206080, 401097277953487040403210240, 401097424330326554129203200, 8202226202151636015513600, 401097424330326554129203200, 19008993687963413438540021760,
    19003924003480401263512780800, 406245780320605919458099200, 314991250121183903505973248, 9763130384203341098523820032, 114598374155315731296606486528, 9763202672273593556772323328,
    315031410160213046977363968, 388698241956341153838137344, 19008986750804883871610437632, 19008993687963413438540021760, 388723678204282899246612480, 8202226202151636015513600,
    388723678204282899246612480, 388620005888329660130918400, 8307507308037513255321600, 26835663573707789904642048, 831769397771932642660319232, 9763202672273593556772323328,
    831775556350410429592240128, 26839085006195449311264768, 388594576424216328425963520, 19003917068172006718502338560, 19003924003480401263512780800, 388620005888329660130918400,
    865912264857397953036288, 26838886285987791494971392, 315031410160213046977363968, 26839085006195449311264768, 866022664972763406532608, 8306963703859241266708480,
    406245632064920936188477440, 406245780320605919458099200, 8307507308037513255321600, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    33, 38, 39, 32, 30, 32,
    33, 35, 29, 40, 44, 45,
    39, 32, 34, 34, 37, 31,
    33, 40, 39, 34, 39, 43,
    44, 38, 33, 34, 35, 37,
    32, 38, 44, 43, 39, 34,
    39, 40, 33, 35, 37, 37,
    40, 34, 39, 45, 44, 40,
    29, 31, 32, 34, 28, 32,
    39, 38, 33, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 16358908703920281, 22970795943322402, 21970796469820861, 17359003110182379, 15259191556827033
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33762195402388670, 38328781049596476, 39328396232584257, 32780595528510646, 30518383113654564, 32472343252751918,
    33025442220820159, 35472353934700256, 29518567039385752, 40374082642407763, 44940668298805099, 45940283481734609,
    39392482768389962, 32472343252751918, 34426303391849576, 34979402376900923, 37426314073797914, 31472527178483103,
    33762195402388670, 40374082642407763, 39374083168906230, 34762289808651362, 39374083168906230, 43940668825303646,
    44940284008233156, 38392483294888429, 33025442220820159, 34979402376900923, 35532501327987025, 37979413058852222,
    32025626146551344, 38328781049596476, 44940668298805099, 43940668825303646, 39328875455858574, 34762289808651362,
    39328875455858574, 40328490638846355, 33780689934773600, 35472353934700256, 37426314073797914, 37979413058852222,
    40426324755746252, 34472537860431441, 39328396232584257, 45940283481734609, 44940284008233156, 40328490638846355,
    29518567039385752, 31472527178483103, 32025626146551344, 34472537860431441, 28518750965116940, 32780595528510646,
    39392482768389962, 38392483294888429, 33780689934773600, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 8556243 / 200000000000
noncomputable def negativeCeiling : ℝ := 19190579 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8201689487073419020206080, coefficient := (-8201689487073419020206080) }, { argument := 388698241956341153838137344, coefficient := (-388698241956341153838137344) }, { argument := 388594576424216328425963520, coefficient := (-388594576424216328425963520) }, { argument := 8306963703859241266708480, coefficient := (-8306963703859241266708480) }, { argument := 865801878815781335072768, coefficient := (-865801878815781335072768) }, { argument := 26835464878832879992307712, coefficient := (-26835464878832879992307712) }, { argument := 314991250121183903505973248, coefficient := (-314991250121183903505973248) }, { argument := 26835663573707789904642048, coefficient := (-26835663573707789904642048) }, { argument := 865912264857397953036288, coefficient := (-865912264857397953036288) }, { argument := 401097277953487040403210240, coefficient := (-401097277953487040403210240) }, { argument := 19008986750804883871610437632, coefficient := (-19008986750804883871610437632) }, { argument := 19003917068172006718502338560, coefficient := (-19003917068172006718502338560) }, { argument := 406245632064920936188477440, coefficient := (-406245632064920936188477440) }, { argument := 26835464878832879992307712, coefficient := (-26835464878832879992307712) }, { argument := 831763239239053801955524608, coefficient := (-831763239239053801955524608) }, { argument := 9763130384203341098523820032, coefficient := (-9763130384203341098523820032) }, { argument := 831769397771932642660319232, coefficient := (-831769397771932642660319232) }, { argument := 26838886285987791494971392, coefficient := (-26838886285987791494971392) }, { argument := 8201689487073419020206080, coefficient := (-8201689487073419020206080) }, { argument := 401097277953487040403210240, coefficient := (-401097277953487040403210240) }, { argument := 401097424330326554129203200, coefficient := (-401097424330326554129203200) }, { argument := 8202226202151636015513600, coefficient := (-8202226202151636015513600) }, { argument := 401097424330326554129203200, coefficient := (-401097424330326554129203200) }, { argument := 19008993687963413438540021760, coefficient := (-19008993687963413438540021760) }, { argument := 19003924003480401263512780800, coefficient := (-19003924003480401263512780800) }, { argument := 406245780320605919458099200, coefficient := (-406245780320605919458099200) }, { argument := 314991250121183903505973248, coefficient := (-314991250121183903505973248) }, { argument := 9763130384203341098523820032, coefficient := (-9763130384203341098523820032) }, { argument := 114598374155315731296606486528, coefficient := (-114598374155315731296606486528) }, { argument := 9763202672273593556772323328, coefficient := (-9763202672273593556772323328) }, { argument := 315031410160213046977363968, coefficient := (-315031410160213046977363968) }, { argument := 388698241956341153838137344, coefficient := (-388698241956341153838137344) }, { argument := 19008986750804883871610437632, coefficient := (-19008986750804883871610437632) }, { argument := 19008993687963413438540021760, coefficient := (-19008993687963413438540021760) }, { argument := 388723678204282899246612480, coefficient := (-388723678204282899246612480) }, { argument := 8202226202151636015513600, coefficient := (-8202226202151636015513600) }, { argument := 388723678204282899246612480, coefficient := (-388723678204282899246612480) }, { argument := 388620005888329660130918400, coefficient := (-388620005888329660130918400) }, { argument := 8307507308037513255321600, coefficient := (-8307507308037513255321600) }, { argument := 26835663573707789904642048, coefficient := (-26835663573707789904642048) }, { argument := 831769397771932642660319232, coefficient := (-831769397771932642660319232) }, { argument := 9763202672273593556772323328, coefficient := (-9763202672273593556772323328) }, { argument := 831775556350410429592240128, coefficient := (-831775556350410429592240128) }, { argument := 26839085006195449311264768, coefficient := (-26839085006195449311264768) }, { argument := 388594576424216328425963520, coefficient := (-388594576424216328425963520) }, { argument := 19003917068172006718502338560, coefficient := (-19003917068172006718502338560) }, { argument := 19003924003480401263512780800, coefficient := (-19003924003480401263512780800) }, { argument := 388620005888329660130918400, coefficient := (-388620005888329660130918400) }, { argument := 865912264857397953036288, coefficient := (-865912264857397953036288) }, { argument := 26838886285987791494971392, coefficient := (-26838886285987791494971392) }, { argument := 315031410160213046977363968, coefficient := (-315031410160213046977363968) }, { argument := 26839085006195449311264768, coefficient := (-26839085006195449311264768) }, { argument := 866022664972763406532608, coefficient := (-866022664972763406532608) }, { argument := 8306963703859241266708480, coefficient := (-8306963703859241266708480) }, { argument := 406245632064920936188477440, coefficient := (-406245632064920936188477440) }, { argument := 406245780320605919458099200, coefficient := (-406245780320605919458099200) }, { argument := 8307507308037513255321600, coefficient := (-8307507308037513255321600) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 1587602943142980285102030848, coefficient := 1587602943142980285102030848 }, { argument := 77640493457990597133408927744, coefficient := 77640493457990597133408927744 }, { argument := 77640521792189494351280209920, coefficient := 77640521792189494351280209920 }, { argument := 1587706835205603417296732160, coefficient := 1587706835205603417296732160 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 740788185434795505382064128, coefficient := 740788185434795505382064128 }] }

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

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9697745045959658693907114360832)
def positiveArguments : Array ℕ := #[
    151941, 222933, 1215537, 19611, 173345, 4107623,
    8213055, 87785
  ]
def positiveCoefficients : Array ℕ := #[
    22960674744758296429253885952, 269509459744148125804771934208, 22960844749951679736481579008, 740882632764452898286338048, 1637197235946077299136266240, 77590804717857842726470418432,
    77570111307929907941144002560, 1658211766794847220337213440
  ]
def positiveScales : Array ℕ := #[
    17, 17, 20, 14, 17, 21,
    22, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    17213151695924778, 17766250663973315, 20213162377873116, 14259375482558218, 17403286698175498, 21969872344780066,
    22969487527773511, 16421686824157693
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 22148683 / 200000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 22960674744758296429253885952, coefficient := 22960674744758296429253885952 }, { argument := 269509459744148125804771934208, coefficient := 269509459744148125804771934208 }, { argument := 22960844749951679736481579008, coefficient := 22960844749951679736481579008 }, { argument := 740882632764452898286338048, coefficient := 740882632764452898286338048 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1637197235946077299136266240, coefficient := 1637197235946077299136266240 }, { argument := 77590804717857842726470418432, coefficient := 77590804717857842726470418432 }, { argument := 77570111307929907941144002560, coefficient := 77570111307929907941144002560 }, { argument := 1658211766794847220337213440, coefficient := 1658211766794847220337213440 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0
