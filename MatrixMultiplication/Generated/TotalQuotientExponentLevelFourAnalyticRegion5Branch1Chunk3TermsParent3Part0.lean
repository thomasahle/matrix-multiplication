import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3

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
def constantNumerator : ℤ := 1494247430821276429059960602624
def positiveArguments : Array ℕ := #[
    11, 1926895, 53056707, 15414213, 2780767, 24470637,
    6117647, 2780925, 188981, 3215495, 70658439, 6422265,
    185405
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 145592069824145680224716062720, 501106429656470570594042118144, 145583125662027125116681322496, 26263601754939949423907569664, 924474527866158450745137954816,
    924472676698497165844214185984, 26265094022748536231795097600, 1784875080598376844258967552, 60738983255339719345653678080, 667350088130978742567161561088, 60656577960213644036674682880,
    1751100715512893141690613760
  ]
def positiveScales : Array ℕ := #[
    3, 20, 25, 23, 21, 24,
    22, 21, 17, 21, 26, 22,
    17
  ]
def negativeArguments : Array ℕ := #[
    582671316881, 619620619481, 217840495416621, 19800865963473, 571576474193, 322636739665,
    22681496429947, 11340724253163, 645310189069, 582671316881, 1002619204135, 582665331745,
    1002619204135, 68239470370043, 749784615223693, 68147066068641, 1967443517065, 22681496429947,
    49901061409869, 399207693159345, 22682785119827, 619620619481, 68239470370043, 19826778130405,
    582665331745, 19826778130405, 108913391342755, 9899897541063, 285779870611, 11340724253163,
    399207693159345, 49900861879409, 2835342149559, 217840495416621, 749784615223693, 108913391342755,
    645310189069, 22682785119827, 2835342149559, 80668362429, 19800865963473, 68147066068641,
    9899897541063, 571576474193, 1967443517065, 285779870611, 5, 3,
    5
  ]
def negativeCoefficients : Array ℕ := #[
    164007395349046737225383936, 5581046382011414989244465152, 61316648374031161086890213376, 5573448285919383753785868288, 160884474761833545212100608, 181628337566415715806740480,
    6384273679382159033192415232, 6384260190082054167887609856, 181638670439345795067019264, 164007395349046737225383936, 564424434267111157787525120, 164005710683030527116574720,
    564424434267111157787525120, 19207703333155353599261278208, 211045607108097157322776772608, 19181693834570261211692138496, 553786118145402005503344640, 6384273679382159033192415232,
    224734401570878266166973825024, 224733952269482680881134960640, 6384636413336119291267776512, 5581046382011414989244465152, 19207703333155353599261278208, 5580741912503091084321095680,
    164005710683030527116574720, 5580741912503091084321095680, 61312788583361052873913794560, 5573146859617177052859334656, 160879764849211020129861632, 6384260190082054167887609856,
    224733952269482680881134960640, 224733502965572961103316516864, 6384622924110886769768005632, 61316648374031161086890213376, 211045607108097157322776772608, 61312788583361052873913794560,
    181638670439345795067019264, 6384636413336119291267776512, 6384622924110886769768005632, 181649003487916259794747392, 5573448285919383753785868288, 19181693834570261211692138496,
    5573146859617177052859334656, 160884474761833545212100608, 553786118145402005503344640, 160879764849211020129861632, 792281625142643375935439503360, 1901475900342344102245054808064,
    792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    39, 39, 47, 44, 39, 38,
    44, 43, 39, 39, 39, 39,
    39, 45, 49, 45, 40, 44,
    45, 48, 44, 39, 45, 44,
    39, 44, 46, 43, 38, 43,
    48, 45, 41, 47, 49, 46,
    39, 44, 41, 36, 44, 45,
    43, 39, 40, 38, 2, 1,
    2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 20877846527852203, 25661031800722547, 23877757896001039, 21407051435897653, 24544548321198022,
    22544545432342788, 21407133405850869, 17527881668757820, 21616609415453756, 26074358541492253, 22614650765109547,
    17500320625508852
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39083891336749205, 39172594198101532, 47630265496935946, 44170628759491557, 39056155580797286, 38231119775851910,
    44366581059920118, 43366578011653721, 39231201848730591, 39083891336749205, 39866910913862647, 39083876517467521,
    39866910913862647, 45955671694451972, 49413469551797560, 45953716790741885, 40839459358352197, 44366581059920118,
    45504135735961659, 48504132851643376, 44366663026896607, 39172594198101532, 45955671694451972, 44172515490883964,
    39083876517467521, 44172515490883964, 46630174678597373, 43170550732753200, 38056113345105761, 43366578011653721,
    48504132851643376, 45504129967303187, 41366659978820311, 47630265496935946, 49413469551797560, 46630174678597373,
    39231201848730591, 44366663026896607, 41366659978820311, 36231283918335500, 44170628759491557, 45953716790741885,
    43170550732753200, 39056155580797286, 40839459358352197, 38056113345105761, 2321928094887363, 1584962500724866,
    2321928094887363
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 1085852287 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1073446311 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 164007395349046737225383936, coefficient := (-164007395349046737225383936) }, { argument := 5581046382011414989244465152, coefficient := (-5581046382011414989244465152) }, { argument := 61316648374031161086890213376, coefficient := (-61316648374031161086890213376) }, { argument := 5573448285919383753785868288, coefficient := (-5573448285919383753785868288) }, { argument := 160884474761833545212100608, coefficient := (-160884474761833545212100608) }, { argument := 181628337566415715806740480, coefficient := (-181628337566415715806740480) }, { argument := 6384273679382159033192415232, coefficient := (-6384273679382159033192415232) }, { argument := 6384260190082054167887609856, coefficient := (-6384260190082054167887609856) }, { argument := 181638670439345795067019264, coefficient := (-181638670439345795067019264) }, { argument := 164007395349046737225383936, coefficient := (-164007395349046737225383936) }, { argument := 564424434267111157787525120, coefficient := (-564424434267111157787525120) }, { argument := 164005710683030527116574720, coefficient := (-164005710683030527116574720) }, { argument := 564424434267111157787525120, coefficient := (-564424434267111157787525120) }, { argument := 19207703333155353599261278208, coefficient := (-19207703333155353599261278208) }, { argument := 211045607108097157322776772608, coefficient := (-211045607108097157322776772608) }, { argument := 19181693834570261211692138496, coefficient := (-19181693834570261211692138496) }, { argument := 553786118145402005503344640, coefficient := (-553786118145402005503344640) }, { argument := 6384273679382159033192415232, coefficient := (-6384273679382159033192415232) }, { argument := 224734401570878266166973825024, coefficient := (-224734401570878266166973825024) }, { argument := 224733952269482680881134960640, coefficient := (-224733952269482680881134960640) }, { argument := 6384636413336119291267776512, coefficient := (-6384636413336119291267776512) }, { argument := 5581046382011414989244465152, coefficient := (-5581046382011414989244465152) }, { argument := 19207703333155353599261278208, coefficient := (-19207703333155353599261278208) }, { argument := 5580741912503091084321095680, coefficient := (-5580741912503091084321095680) }, { argument := 164005710683030527116574720, coefficient := (-164005710683030527116574720) }, { argument := 5580741912503091084321095680, coefficient := (-5580741912503091084321095680) }, { argument := 61312788583361052873913794560, coefficient := (-61312788583361052873913794560) }, { argument := 5573146859617177052859334656, coefficient := (-5573146859617177052859334656) }, { argument := 160879764849211020129861632, coefficient := (-160879764849211020129861632) }, { argument := 6384260190082054167887609856, coefficient := (-6384260190082054167887609856) }, { argument := 224733952269482680881134960640, coefficient := (-224733952269482680881134960640) }, { argument := 224733502965572961103316516864, coefficient := (-224733502965572961103316516864) }, { argument := 6384622924110886769768005632, coefficient := (-6384622924110886769768005632) }, { argument := 61316648374031161086890213376, coefficient := (-61316648374031161086890213376) }, { argument := 211045607108097157322776772608, coefficient := (-211045607108097157322776772608) }, { argument := 61312788583361052873913794560, coefficient := (-61312788583361052873913794560) }, { argument := 181638670439345795067019264, coefficient := (-181638670439345795067019264) }, { argument := 6384636413336119291267776512, coefficient := (-6384636413336119291267776512) }, { argument := 6384622924110886769768005632, coefficient := (-6384622924110886769768005632) }, { argument := 181649003487916259794747392, coefficient := (-181649003487916259794747392) }, { argument := 5573448285919383753785868288, coefficient := (-5573448285919383753785868288) }, { argument := 19181693834570261211692138496, coefficient := (-19181693834570261211692138496) }, { argument := 5573146859617177052859334656, coefficient := (-5573146859617177052859334656) }, { argument := 160884474761833545212100608, coefficient := (-160884474761833545212100608) }, { argument := 553786118145402005503344640, coefficient := (-553786118145402005503344640) }, { argument := 160879764849211020129861632, coefficient := (-160879764849211020129861632) }, { argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 145592069824145680224716062720, coefficient := 145592069824145680224716062720 }, { argument := 501106429656470570594042118144, coefficient := 501106429656470570594042118144 }, { argument := 145583125662027125116681322496, coefficient := 145583125662027125116681322496 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 26263601754939949423907569664, coefficient := 26263601754939949423907569664 }, { argument := 924474527866158450745137954816, coefficient := 924474527866158450745137954816 }, { argument := 924472676698497165844214185984, coefficient := 924472676698497165844214185984 }, { argument := 26265094022748536231795097600, coefficient := 26265094022748536231795097600 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 1784875080598376844258967552, coefficient := 1784875080598376844258967552 }, { argument := 60738983255339719345653678080, coefficient := 60738983255339719345653678080 }, { argument := 667350088130978742567161561088, coefficient := 667350088130978742567161561088 }, { argument := 60656577960213644036674682880, coefficient := 60656577960213644036674682880 }, { argument := 1751100715512893141690613760, coefficient := 1751100715512893141690613760 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3
