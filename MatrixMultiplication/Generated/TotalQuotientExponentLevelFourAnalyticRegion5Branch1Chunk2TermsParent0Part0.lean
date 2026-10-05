import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-470340639641856295083337318400)
def positiveArguments : Array ℕ := #[
    7, 2097147, 2097157, 18605357, 31721645, 18614649,
    1292609, 49039119, 24519403, 646381, 38201, 1276761,
    7073665, 638373, 19089
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 79227973619605022807735402496, 79228351408923652379352498176, 175722628597248267328310738944, 599204932517957866979254599680, 175810389055965916814962065408,
    12208346834111298460060745728, 463161383830111986244437147648, 463158427628693709846533373952, 12209791878255056571496136704, 360798244024206633616801792, 12058666706070262185367437312,
    133617754028192435642155663360, 12058525035075776096011026432, 360581015165994629936971776
  ]
def positiveScales : Array ℕ := #[
    2, 20, 21, 24, 24, 24,
    20, 25, 24, 19, 15, 20,
    22, 19, 14
  ]
def negativeArguments : Array ℕ := #[
    80113112547, 2677555500867, 14834515333755, 1338762021831, 40032439083, 4008709476867,
    152064584984905, 76031807587757, 2004591754413, 4008709476867, 13666827969629, 125338842189,
    80113112547, 80113494557, 80113494557, 2677568268477, 14834586070405, 1338768405561,
    40032629973, 13666827969629, 518534908361891, 259265798506973, 6834223367587, 152064584984905,
    518534908361891, 38035099641477, 2677555500867, 2677568268477, 125338842189, 38035099641477,
    38034857113659, 125353658331, 76031807587757, 259265798506973, 38034857113659, 14834515333755,
    14834586070405, 2004591754413, 6834223367587, 125353658331, 1338762021831, 1338768405561,
    40032439083, 40032629973, 1, 3, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    90199345953539951928803328, 3014659488992110744864555008, 33404358864660463551239946240, 3014624071327931715538649088, 90145038868465440295747584, 1128351406640924822184394752,
    42802375517141704944312647680, 42802102540065959443834077184, 1128484834775544453824249856, 1128351406640924822184394752, 3846870084459864801488666624, 1128951925954859606357311488,
    90199345953539951928803328, 90199776058563364879597568, 90199776058563364879597568, 3014673864043020347819163648, 33404518149435754269837885440, 3014638446209956332466864128,
    90145468714531874672738304, 3846870084459864801488666624, 145954601254825412376444010496, 145953669193239712622838808576, 3847325726453943688855814144, 42802375517141704944312647680,
    145954601254825412376444010496, 42823715143088875801461915648, 3014659488992110744864555008, 3014673864043020347819163648, 1128951925954859606357311488, 42823715143088875801461915648,
    42823442081041182856593801216, 1129085377898040143068004352, 42802102540065959443834077184, 145953669193239712622838808576, 42823442081041182856593801216, 33404358864660463551239946240,
    33404518149435754269837885440, 1128484834775544453824249856, 3847325726453943688855814144, 1129085377898040143068004352, 3014624071327931715538649088, 3014638446209956332466864128,
    90145038868465440295747584, 90145468714531874672738304, 158456325028528675187087900672, 950737950171172051122527404032, 950737950171172051122527404032, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    36, 41, 43, 40, 35, 41,
    47, 46, 40, 41, 43, 36,
    36, 36, 36, 41, 43, 40,
    35, 43, 48, 47, 42, 47,
    48, 45, 41, 41, 36, 45,
    45, 36, 46, 47, 45, 43,
    43, 40, 42, 36, 40, 40,
    35, 35, 0, 1, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 20999996558883380, 21000003439648916, 24149214737405038, 24918964251137032, 24149935077030907,
    20301854511086057, 25547429725096842, 24547420516836210, 19302025265953744, 15221322784202037, 20284057058041302,
    22754026465718032, 19284040108469115, 14220453906972867
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36221319344544921, 41284053618384186, 43754023026321627, 40284036668811999, 35220450467315750, 41866275005868317,
    47111677524773863, 46111668323790868, 40866445595221069, 41866275005868317, 43635743670092516, 36867042617631000,
    36221319344544921, 36221326223850956, 36221326223850956, 41284060497690220, 43754029905627699, 40284043548118033,
    35220457346621785, 43635743670092516, 48881434447726901, 47881425234690885, 42635914539787662, 47111677524773863,
    48881434447726901, 45112396618053222, 41284053618384186, 41284060497690220, 36867042617631000, 45112396618053222,
    45112387418792562, 36867213146669759, 46111668323790868, 47881425234690885, 45112387418792562, 43754023026321627,
    43754029905627699, 40866445595221069, 42635914539787662, 36867213146669759, 40284036668811999, 40284043548118033,
    35220450467315750, 35220457346621785, 0, 1584962500724866, 1584962500724866, 0
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
noncomputable def positiveFloor : ℝ := 687027053 / 1000000000000
noncomputable def negativeCeiling : ℝ := 660114411 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 90199345953539951928803328, coefficient := (-90199345953539951928803328) }, { argument := 3014659488992110744864555008, coefficient := (-3014659488992110744864555008) }, { argument := 33404358864660463551239946240, coefficient := (-33404358864660463551239946240) }, { argument := 3014624071327931715538649088, coefficient := (-3014624071327931715538649088) }, { argument := 90145038868465440295747584, coefficient := (-90145038868465440295747584) }, { argument := 1128351406640924822184394752, coefficient := (-1128351406640924822184394752) }, { argument := 42802375517141704944312647680, coefficient := (-42802375517141704944312647680) }, { argument := 42802102540065959443834077184, coefficient := (-42802102540065959443834077184) }, { argument := 1128484834775544453824249856, coefficient := (-1128484834775544453824249856) }, { argument := 1128351406640924822184394752, coefficient := (-1128351406640924822184394752) }, { argument := 3846870084459864801488666624, coefficient := (-3846870084459864801488666624) }, { argument := 1128951925954859606357311488, coefficient := (-1128951925954859606357311488) }, { argument := 90199345953539951928803328, coefficient := (-90199345953539951928803328) }, { argument := 90199776058563364879597568, coefficient := (-90199776058563364879597568) }, { argument := 90199776058563364879597568, coefficient := (-90199776058563364879597568) }, { argument := 3014673864043020347819163648, coefficient := (-3014673864043020347819163648) }, { argument := 33404518149435754269837885440, coefficient := (-33404518149435754269837885440) }, { argument := 3014638446209956332466864128, coefficient := (-3014638446209956332466864128) }, { argument := 90145468714531874672738304, coefficient := (-90145468714531874672738304) }, { argument := 3846870084459864801488666624, coefficient := (-3846870084459864801488666624) }, { argument := 145954601254825412376444010496, coefficient := (-145954601254825412376444010496) }, { argument := 145953669193239712622838808576, coefficient := (-145953669193239712622838808576) }, { argument := 3847325726453943688855814144, coefficient := (-3847325726453943688855814144) }, { argument := 42802375517141704944312647680, coefficient := (-42802375517141704944312647680) }, { argument := 145954601254825412376444010496, coefficient := (-145954601254825412376444010496) }, { argument := 42823715143088875801461915648, coefficient := (-42823715143088875801461915648) }, { argument := 3014659488992110744864555008, coefficient := (-3014659488992110744864555008) }, { argument := 3014673864043020347819163648, coefficient := (-3014673864043020347819163648) }, { argument := 1128951925954859606357311488, coefficient := (-1128951925954859606357311488) }, { argument := 42823715143088875801461915648, coefficient := (-42823715143088875801461915648) }, { argument := 42823442081041182856593801216, coefficient := (-42823442081041182856593801216) }, { argument := 1129085377898040143068004352, coefficient := (-1129085377898040143068004352) }, { argument := 42802102540065959443834077184, coefficient := (-42802102540065959443834077184) }, { argument := 145953669193239712622838808576, coefficient := (-145953669193239712622838808576) }, { argument := 42823442081041182856593801216, coefficient := (-42823442081041182856593801216) }, { argument := 33404358864660463551239946240, coefficient := (-33404358864660463551239946240) }, { argument := 33404518149435754269837885440, coefficient := (-33404518149435754269837885440) }, { argument := 1128484834775544453824249856, coefficient := (-1128484834775544453824249856) }, { argument := 3847325726453943688855814144, coefficient := (-3847325726453943688855814144) }, { argument := 1129085377898040143068004352, coefficient := (-1129085377898040143068004352) }, { argument := 3014624071327931715538649088, coefficient := (-3014624071327931715538649088) }, { argument := 3014638446209956332466864128, coefficient := (-3014638446209956332466864128) }, { argument := 90145038868465440295747584, coefficient := (-90145038868465440295747584) }, { argument := 90145468714531874672738304, coefficient := (-90145468714531874672738304) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 79227973619605022807735402496, coefficient := 79227973619605022807735402496 }, { argument := 79228351408923652379352498176, coefficient := 79228351408923652379352498176 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 175722628597248267328310738944, coefficient := 175722628597248267328310738944 }, { argument := 599204932517957866979254599680, coefficient := 599204932517957866979254599680 }, { argument := 175810389055965916814962065408, coefficient := 175810389055965916814962065408 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 12208346834111298460060745728, coefficient := 12208346834111298460060745728 }, { argument := 463161383830111986244437147648, coefficient := 463161383830111986244437147648 }, { argument := 463158427628693709846533373952, coefficient := 463158427628693709846533373952 }, { argument := 12209791878255056571496136704, coefficient := 12209791878255056571496136704 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 360798244024206633616801792, coefficient := 360798244024206633616801792 }, { argument := 12058666706070262185367437312, coefficient := 12058666706070262185367437312 }, { argument := 133617754028192435642155663360, coefficient := 133617754028192435642155663360 }, { argument := 12058525035075776096011026432, coefficient := 12058525035075776096011026432 }, { argument := 360581015165994629936971776, coefficient := 360581015165994629936971776 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2
