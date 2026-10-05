import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 3, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3

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
def constantNumerator : ℤ := (-467670191227034642359613652992)
def positiveArguments : Array ℕ := #[
    9, 16776665, 16777767, 1884977, 53722943, 15083321,
    189395, 8199211, 4100567, 46869
  ]
def positiveCoefficients : Array ℕ := #[
    713053462628379038341895553024, 158451120980664552838062407680, 158461529076392797536113393664, 142424835292482803615632719872, 507398850768632852491226054656, 142457939081527719828580728832,
    3577570400092385820991815680, 154878716849504426408934375424, 154915041292490659719918125056, 3541321514969878424331485184
  ]
def positiveScales : Array ℕ := #[
    3, 23, 24, 20, 25, 23,
    17, 22, 21, 15
  ]
def negativeArguments : Array ℕ := #[
    3177428698025, 137555403980965, 8599229126685, 1572616879345, 45479304873399, 81014046852841,
    45489931693175, 3177428698025, 3177612950615, 3177612950615, 137564463972187, 8599795443683,
    1572708467471, 81014046852841, 577227680215353, 162065644945653, 137555403980965, 137564463972187,
    45489931693175, 162065644945653, 11375139443877, 8599229126685, 8599795443683, 1572616879345,
    1572708467471, 1, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    894366668776356891223654400, 38718404131967001003336663040, 38727485090612081741015285760, 885304598976836783455600640, 12801286280056807447534239744, 45606853902278828974137147392,
    12804277463905765386144972800, 894366668776356891223654400, 894418531269836019272253440, 894418531269836019272253440, 38720954292785212201130524672, 38730035555633248118943776768,
    885356158508102428710141952, 45606853902278828974137147392, 162475147845362474817649901568, 45617423636675122453825978368, 38718404131967001003336663040, 38720954292785212201130524672,
    12804277463905765386144972800, 45617423636675122453825978368, 12807268440182972074319413248, 38727485090612081741015285760, 38730035555633248118943776768, 885304598976836783455600640,
    885356158508102428710141952, 316912650057057350374175801344, 792281625142643375935439503360, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    41, 46, 42, 40, 45, 46,
    45, 41, 41, 41, 46, 42,
    40, 46, 49, 47, 46, 46,
    45, 47, 43, 42, 42, 40,
    40, 0, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 23999952616543138, 24000047380442278, 20846115489435628, 25679035003508923, 23846450775923330,
    17531038718810006, 22967053656107607, 21967391978568143, 15516346393260500
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41530996889950163, 46967006160543783, 42967344488561128, 40516304383088932, 45370275437120226, 46203237309038548,
    45370612501843195, 41530996889950163, 41531080546458693, 41531080546458693, 46967101179544106, 42967439496613476,
    40516388402209789, 46203237309038548, 49036133812507054, 47203571625820805, 46967006160543783, 46967101179544106,
    45370612501843195, 47203571625820805, 43370949464452037, 42967344488561128, 42967439496613476, 40516304383088932,
    40516388402209789, 0, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 10
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
noncomputable def positiveFloor : ℝ := 109355859 / 250000000000
noncomputable def negativeCeiling : ℝ := 419472891 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 894366668776356891223654400, coefficient := (-894366668776356891223654400) }, { argument := 38718404131967001003336663040, coefficient := (-38718404131967001003336663040) }, { argument := 38727485090612081741015285760, coefficient := (-38727485090612081741015285760) }, { argument := 885304598976836783455600640, coefficient := (-885304598976836783455600640) }, { argument := 12801286280056807447534239744, coefficient := (-12801286280056807447534239744) }, { argument := 45606853902278828974137147392, coefficient := (-45606853902278828974137147392) }, { argument := 12804277463905765386144972800, coefficient := (-12804277463905765386144972800) }, { argument := 894366668776356891223654400, coefficient := (-894366668776356891223654400) }, { argument := 894418531269836019272253440, coefficient := (-894418531269836019272253440) }, { argument := 894418531269836019272253440, coefficient := (-894418531269836019272253440) }, { argument := 38720954292785212201130524672, coefficient := (-38720954292785212201130524672) }, { argument := 38730035555633248118943776768, coefficient := (-38730035555633248118943776768) }, { argument := 885356158508102428710141952, coefficient := (-885356158508102428710141952) }, { argument := 45606853902278828974137147392, coefficient := (-45606853902278828974137147392) }, { argument := 162475147845362474817649901568, coefficient := (-162475147845362474817649901568) }, { argument := 45617423636675122453825978368, coefficient := (-45617423636675122453825978368) }, { argument := 38718404131967001003336663040, coefficient := (-38718404131967001003336663040) }, { argument := 38720954292785212201130524672, coefficient := (-38720954292785212201130524672) }, { argument := 12804277463905765386144972800, coefficient := (-12804277463905765386144972800) }, { argument := 45617423636675122453825978368, coefficient := (-45617423636675122453825978368) }, { argument := 12807268440182972074319413248, coefficient := (-12807268440182972074319413248) }, { argument := 38727485090612081741015285760, coefficient := (-38727485090612081741015285760) }, { argument := 38730035555633248118943776768, coefficient := (-38730035555633248118943776768) }, { argument := 885304598976836783455600640, coefficient := (-885304598976836783455600640) }, { argument := 885356158508102428710141952, coefficient := (-885356158508102428710141952) }, { argument := 713053462628379038341895553024, coefficient := 713053462628379038341895553024 }, { argument := 158451120980664552838062407680, coefficient := 158451120980664552838062407680 }, { argument := 158461529076392797536113393664, coefficient := 158461529076392797536113393664 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 142424835292482803615632719872, coefficient := 142424835292482803615632719872 }, { argument := 507398850768632852491226054656, coefficient := 507398850768632852491226054656 }, { argument := 142457939081527719828580728832, coefficient := 142457939081527719828580728832 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 3577570400092385820991815680, coefficient := 3577570400092385820991815680 }, { argument := 154878716849504426408934375424, coefficient := 154878716849504426408934375424 }, { argument := 154915041292490659719918125056, coefficient := 154915041292490659719918125056 }, { argument := 3541321514969878424331485184, coefficient := 3541321514969878424331485184 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3
