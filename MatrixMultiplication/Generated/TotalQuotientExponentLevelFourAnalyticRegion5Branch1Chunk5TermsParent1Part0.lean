import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 5, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5

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
def constantNumerator : ℤ := 3453065274556378150829411008512
def positiveArguments : Array ℕ := #[
    3, 8388589, 8388627, 3843677, 106282289, 30740455,
    1195103, 81495829, 5093489, 2390301, 20585, 2597081,
    28199681, 2596543, 78787
  ]
def positiveCoefficients : Array ℕ := #[
    1901475900342344102245054808064, 158455966128675977094051659776, 158456683928381373280124141568, 290420022972431188896694403072, 1003807838592530363859010060288, 290335388720325199115174543360,
    22574857403107846415294922752, 769706342726552071252075347968, 769706295502887242555623211008, 22575754652739591647885524992, 777679312398973173791457280, 24528736535395162122461642752,
    266338456764031919218808061952, 24523655269059594384211705856, 744122176171701474902933504
  ]
def positiveScales : Array ℕ := #[
    1, 22, 23, 21, 26, 24,
    20, 26, 22, 21, 14, 21,
    24, 21, 16
  ]
def negativeArguments : Array ℕ := #[
    86339550545, 2723230633597, 14784720871991, 5445333000065, 165227937799, 3675881186999,
    250592892593725, 31324110577579, 7352054517501, 3675881186999, 25399561382663, 7349678589835,
    86339550545, 86339945135, 86339945135, 2723242979715, 14784787832265, 5445357691007,
    165228691449, 25399561382663, 433080213874603, 433080179672087, 25400571051381, 250592892593725,
    433080213874603, 250519805889133, 2723230633597, 2723242979715, 7349678589835, 250519805889133,
    125259899190589, 3674985306567, 31324110577579, 433080179672087, 125259899190589, 14784720871991,
    14784787832265, 7352054517501, 25400571051381, 3674985306567, 5445333000065, 5445357691007,
    165227937799, 165228691449, 1, 5, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    194419383830899052416860160, 6132170233355684462572077056, 66584463409875462291546177536, 6130899917500249767736770560, 186030119775692972753944576, 2069337143003364115703922688,
    70535628606674664804686233600, 70535626362448498317791854592, 2069419374089067210165190656, 2069337143003364115703922688, 7149340948645945435045756928, 2068750609904613656897781760,
    194419383830899052416860160, 194420272368587534478868480, 194420272368587534478868480, 6132198034341896598658744320, 66584764972140497317857853440, 6130927717029547424369082368,
    186030968310157764697522176, 7149340948645945435045756928, 243802486228399597811595739136, 243802466974094808719917318144, 7149625145124829962946215936, 70535628606674664804686233600,
    243802486228399597811595739136, 70515056528201773009755701248, 6132170233355684462572077056, 6132198034341896598658744320, 2068750609904613656897781760, 70515056528201773009755701248,
    70515054414900314240102432768, 2068832807155898650831355904, 70535626362448498317791854592, 243802466974094808719917318144, 70515054414900314240102432768, 66584463409875462291546177536,
    66584764972140497317857853440, 2069419374089067210165190656, 7149625145124829962946215936, 2068832807155898650831355904, 6130899917500249767736770560, 6130927717029547424369082368,
    186030119775692972753944576, 186030968310157764697522176, 316912650057057350374175801344, 1584563250285286751870879006720, 1584563250285286751870879006720, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    36, 41, 43, 42, 37, 41,
    47, 44, 42, 41, 44, 42,
    36, 36, 36, 41, 43, 42,
    37, 44, 48, 48, 44, 47,
    48, 47, 41, 41, 42, 47,
    46, 41, 44, 48, 46, 43,
    43, 42, 44, 41, 42, 42,
    37, 37, 0, 2, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 22999996730866427, 23000003267666665, 21874055674758287, 26663325963673286, 24873635183054448,
    20188703531618551, 26280222887542958, 22280222799029527, 21188760871155509, 14329305828208631, 21308459580058227,
    24749175506881441, 21308160686670961, 16265669981531174
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36329302531501723, 41308456309739732, 43749172240123439, 42308157415846276, 37265666691270787, 41741227274966294,
    47832338826656094, 44832338780753986, 42741284603480094, 41741227274966294, 44529868817285022, 42740818299394708,
    36329302531501723, 36329309124908009, 36329309124908009, 41308462850369313, 43749178774101171, 42308163957488233,
    37265673271784061, 44529868817285022, 48621627589970446, 48621627476033580, 44529926165326566, 47832338826656094,
    48621627589970446, 47831917995853510, 41308456309739732, 41308462850369313, 42740818299394708, 47831917995853510,
    46831917952616649, 41740875620567648, 44832338780753986, 48621627476033580, 46831917952616649, 43749172240123439,
    43749178774101171, 42741284603480094, 44529926165326566, 41740875620567648, 42308157415846276, 42308163957488233,
    37265666691270787, 37265673271784061, 0, 2321928094887363, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 232588527 / 200000000000
noncomputable def negativeCeiling : ℝ := 1166741381 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 194419383830899052416860160, coefficient := (-194419383830899052416860160) }, { argument := 6132170233355684462572077056, coefficient := (-6132170233355684462572077056) }, { argument := 66584463409875462291546177536, coefficient := (-66584463409875462291546177536) }, { argument := 6130899917500249767736770560, coefficient := (-6130899917500249767736770560) }, { argument := 186030119775692972753944576, coefficient := (-186030119775692972753944576) }, { argument := 2069337143003364115703922688, coefficient := (-2069337143003364115703922688) }, { argument := 70535628606674664804686233600, coefficient := (-70535628606674664804686233600) }, { argument := 70535626362448498317791854592, coefficient := (-70535626362448498317791854592) }, { argument := 2069419374089067210165190656, coefficient := (-2069419374089067210165190656) }, { argument := 2069337143003364115703922688, coefficient := (-2069337143003364115703922688) }, { argument := 7149340948645945435045756928, coefficient := (-7149340948645945435045756928) }, { argument := 2068750609904613656897781760, coefficient := (-2068750609904613656897781760) }, { argument := 194419383830899052416860160, coefficient := (-194419383830899052416860160) }, { argument := 194420272368587534478868480, coefficient := (-194420272368587534478868480) }, { argument := 194420272368587534478868480, coefficient := (-194420272368587534478868480) }, { argument := 6132198034341896598658744320, coefficient := (-6132198034341896598658744320) }, { argument := 66584764972140497317857853440, coefficient := (-66584764972140497317857853440) }, { argument := 6130927717029547424369082368, coefficient := (-6130927717029547424369082368) }, { argument := 186030968310157764697522176, coefficient := (-186030968310157764697522176) }, { argument := 7149340948645945435045756928, coefficient := (-7149340948645945435045756928) }, { argument := 243802486228399597811595739136, coefficient := (-243802486228399597811595739136) }, { argument := 243802466974094808719917318144, coefficient := (-243802466974094808719917318144) }, { argument := 7149625145124829962946215936, coefficient := (-7149625145124829962946215936) }, { argument := 70535628606674664804686233600, coefficient := (-70535628606674664804686233600) }, { argument := 243802486228399597811595739136, coefficient := (-243802486228399597811595739136) }, { argument := 70515056528201773009755701248, coefficient := (-70515056528201773009755701248) }, { argument := 6132170233355684462572077056, coefficient := (-6132170233355684462572077056) }, { argument := 6132198034341896598658744320, coefficient := (-6132198034341896598658744320) }, { argument := 2068750609904613656897781760, coefficient := (-2068750609904613656897781760) }, { argument := 70515056528201773009755701248, coefficient := (-70515056528201773009755701248) }, { argument := 70515054414900314240102432768, coefficient := (-70515054414900314240102432768) }, { argument := 2068832807155898650831355904, coefficient := (-2068832807155898650831355904) }, { argument := 70535626362448498317791854592, coefficient := (-70535626362448498317791854592) }, { argument := 243802466974094808719917318144, coefficient := (-243802466974094808719917318144) }, { argument := 70515054414900314240102432768, coefficient := (-70515054414900314240102432768) }, { argument := 66584463409875462291546177536, coefficient := (-66584463409875462291546177536) }, { argument := 66584764972140497317857853440, coefficient := (-66584764972140497317857853440) }, { argument := 2069419374089067210165190656, coefficient := (-2069419374089067210165190656) }, { argument := 7149625145124829962946215936, coefficient := (-7149625145124829962946215936) }, { argument := 2068832807155898650831355904, coefficient := (-2068832807155898650831355904) }, { argument := 6130899917500249767736770560, coefficient := (-6130899917500249767736770560) }, { argument := 6130927717029547424369082368, coefficient := (-6130927717029547424369082368) }, { argument := 186030119775692972753944576, coefficient := (-186030119775692972753944576) }, { argument := 186030968310157764697522176, coefficient := (-186030968310157764697522176) }, { argument := 1901475900342344102245054808064, coefficient := 1901475900342344102245054808064 }, { argument := 158455966128675977094051659776, coefficient := 158455966128675977094051659776 }, { argument := 158456683928381373280124141568, coefficient := 158456683928381373280124141568 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 290420022972431188896694403072, coefficient := 290420022972431188896694403072 }, { argument := 1003807838592530363859010060288, coefficient := 1003807838592530363859010060288 }, { argument := 290335388720325199115174543360, coefficient := 290335388720325199115174543360 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 22574857403107846415294922752, coefficient := 22574857403107846415294922752 }, { argument := 769706342726552071252075347968, coefficient := 769706342726552071252075347968 }, { argument := 769706295502887242555623211008, coefficient := 769706295502887242555623211008 }, { argument := 22575754652739591647885524992, coefficient := 22575754652739591647885524992 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 777679312398973173791457280, coefficient := 777679312398973173791457280 }, { argument := 24528736535395162122461642752, coefficient := 24528736535395162122461642752 }, { argument := 266338456764031919218808061952, coefficient := 266338456764031919218808061952 }, { argument := 24523655269059594384211705856, coefficient := 24523655269059594384211705856 }, { argument := 744122176171701474902933504, coefficient := 744122176171701474902933504 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5
