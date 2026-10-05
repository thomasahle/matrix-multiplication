import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 3, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3

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
def constantNumerator : ℤ := 3093082200067494666332815753216
def positiveArguments : Array ℕ := #[
    3, 3773691, 6712585, 3772659, 1572287, 114295887,
    114296021, 1572271, 131049, 6428813, 35257491, 3211675,
    256837
  ]
def positiveCoefficients : Array ℕ := #[
    1901475900342344102245054808064, 142566015160854674528941375488, 507188582678616598668441026560, 142527027303172102738057101312, 29699661721006663456425771008, 1079494131797312810149377736704,
    1079495397391530219214295007232, 29699359489551759799132094464, 2475445620854336542438588416, 60718422071673304910393245696, 665995175073912681180319186944, 60666825495481471166788403200,
    2425756880721582135500079104
  ]
def positiveScales : Array ℕ := #[
    1, 21, 22, 21, 20, 26,
    26, 20, 16, 22, 25, 21,
    17
  ]
def negativeArguments : Array ℕ := #[
    395461164773, 9706425299177, 26609100355429, 9698239422617, 387530740229, 89069688273,
    12833013516703, 12833032302091, 178137020553, 395461164773, 1407847061389, 197664576711,
    1407847061389, 17259108348643, 378679568691449, 17244372770365, 689787931293, 12833013516703,
    233279237819359, 233279509444109, 12832884011657, 9706425299177, 17259108348643, 9704150165841,
    197664576711, 9704150165841, 106406572011891, 9695980233453, 387398310081, 12833032302091,
    233279509444109, 233279781071403, 12832902795653, 26609100355429, 378679568691449, 106406572011891,
    178137020553, 12832884011657, 12832902795653, 11133416535, 9698239422617, 17244372770365,
    9695980233453, 387530740229, 689787931293, 387398310081, 5, 7,
    5
  ]
def negativeCoefficients : Array ℕ := #[
    222624844288898139921842176, 5464231670059136544327860224, 59918367222687088535134011392, 5459623431230971934622613504, 218160412161242110464360448, 200567107458144518698696704,
    7224344361483021155708174336, 7224354936716320756981563392, 200564454845845296824451072, 222624844288898139921842176, 792547437633268525844922368, 222550528505001605452529664,
    792547437633268525844922368, 19432028481923907840724959232, 213177645556453732496428761088, 19415437695713435446946037760, 776632167583955024275832832, 7224344361483021155708174336,
    262649072129134627568553558016, 262649377951415348719586902016, 7224271456623407630840233984, 5464231670059136544327860224, 19432028481923907840724959232, 5462950883853608070143803392,
    222550528505001605452529664, 5462950883853608070143803392, 59901574757815519558596820992, 5458351620796328201825550336, 218085860615593933009846272, 7224354936716320756981563392,
    262649377951415348719586902016, 262649683776560359233627881472, 7224282031073080896951156736, 59918367222687088535134011392, 213177645556453732496428761088, 59901574757815519558596820992,
    200564454845845296824451072, 7224271456623407630840233984, 7224282031073080896951156736, 200561802233546074950205440, 5459623431230971934622613504, 19415437695713435446946037760,
    5458351620796328201825550336, 218160412161242110464360448, 776632167583955024275832832, 218085860615593933009846272, 792281625142643375935439503360, 2218388550399401452619230609408,
    792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    38, 43, 44, 43, 38, 36,
    43, 43, 37, 38, 40, 37,
    40, 43, 48, 43, 39, 43,
    47, 47, 43, 43, 43, 43,
    37, 43, 46, 43, 38, 43,
    47, 47, 43, 44, 48, 46,
    37, 43, 43, 33, 43, 43,
    43, 38, 39, 38, 2, 2,
    2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 21847544865234307, 22678437021067890, 21847150274130375, 20584433155676488, 26768198247394706,
    26768199938803094, 20584418474363150, 16999746817869993, 22616120955850764, 25071426477194980, 21614894478489259,
    17970493525958123
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38524745069331150, 43142077213624871, 44596984967700297, 43140860008959054, 38495519798062782, 36374215493769424,
    43544925225094724, 43544927336957712, 37374196413193527, 38524745069331150, 40356627756885058, 37524263393926635,
    40356627756885058, 43972423181669645, 48427970912458496, 43971190902980212, 39327361931017196, 43544925225094724,
    47729051239710040, 47729052919548574, 43544910665986675, 43142077213624871, 43972423181669645, 43141739014110678,
    37524263393926635, 43141739014110678, 46596580587501873, 43140523896336234, 38495026704354219, 43544927336957712,
    47729052919548574, 47729054599400885, 43544912777714485, 44596984967700297, 48427970912458496, 46596580587501873,
    37374196413193527, 43544910665986675, 43544912777714485, 33374177332365274, 43140860008959054, 43971190902980212,
    43140523896336234, 38495519798062782, 39327361931017196, 38495026704354219, 2321928094887363, 2807354922807594,
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
noncomputable def positiveFloor : ℝ := 1194403259 / 1000000000000
noncomputable def negativeCeiling : ℝ := 299917681 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 222624844288898139921842176, coefficient := (-222624844288898139921842176) }, { argument := 5464231670059136544327860224, coefficient := (-5464231670059136544327860224) }, { argument := 59918367222687088535134011392, coefficient := (-59918367222687088535134011392) }, { argument := 5459623431230971934622613504, coefficient := (-5459623431230971934622613504) }, { argument := 218160412161242110464360448, coefficient := (-218160412161242110464360448) }, { argument := 200567107458144518698696704, coefficient := (-200567107458144518698696704) }, { argument := 7224344361483021155708174336, coefficient := (-7224344361483021155708174336) }, { argument := 7224354936716320756981563392, coefficient := (-7224354936716320756981563392) }, { argument := 200564454845845296824451072, coefficient := (-200564454845845296824451072) }, { argument := 222624844288898139921842176, coefficient := (-222624844288898139921842176) }, { argument := 792547437633268525844922368, coefficient := (-792547437633268525844922368) }, { argument := 222550528505001605452529664, coefficient := (-222550528505001605452529664) }, { argument := 792547437633268525844922368, coefficient := (-792547437633268525844922368) }, { argument := 19432028481923907840724959232, coefficient := (-19432028481923907840724959232) }, { argument := 213177645556453732496428761088, coefficient := (-213177645556453732496428761088) }, { argument := 19415437695713435446946037760, coefficient := (-19415437695713435446946037760) }, { argument := 776632167583955024275832832, coefficient := (-776632167583955024275832832) }, { argument := 7224344361483021155708174336, coefficient := (-7224344361483021155708174336) }, { argument := 262649072129134627568553558016, coefficient := (-262649072129134627568553558016) }, { argument := 262649377951415348719586902016, coefficient := (-262649377951415348719586902016) }, { argument := 7224271456623407630840233984, coefficient := (-7224271456623407630840233984) }, { argument := 5464231670059136544327860224, coefficient := (-5464231670059136544327860224) }, { argument := 19432028481923907840724959232, coefficient := (-19432028481923907840724959232) }, { argument := 5462950883853608070143803392, coefficient := (-5462950883853608070143803392) }, { argument := 222550528505001605452529664, coefficient := (-222550528505001605452529664) }, { argument := 5462950883853608070143803392, coefficient := (-5462950883853608070143803392) }, { argument := 59901574757815519558596820992, coefficient := (-59901574757815519558596820992) }, { argument := 5458351620796328201825550336, coefficient := (-5458351620796328201825550336) }, { argument := 218085860615593933009846272, coefficient := (-218085860615593933009846272) }, { argument := 7224354936716320756981563392, coefficient := (-7224354936716320756981563392) }, { argument := 262649377951415348719586902016, coefficient := (-262649377951415348719586902016) }, { argument := 262649683776560359233627881472, coefficient := (-262649683776560359233627881472) }, { argument := 7224282031073080896951156736, coefficient := (-7224282031073080896951156736) }, { argument := 59918367222687088535134011392, coefficient := (-59918367222687088535134011392) }, { argument := 213177645556453732496428761088, coefficient := (-213177645556453732496428761088) }, { argument := 59901574757815519558596820992, coefficient := (-59901574757815519558596820992) }, { argument := 200564454845845296824451072, coefficient := (-200564454845845296824451072) }, { argument := 7224271456623407630840233984, coefficient := (-7224271456623407630840233984) }, { argument := 7224282031073080896951156736, coefficient := (-7224282031073080896951156736) }, { argument := 200561802233546074950205440, coefficient := (-200561802233546074950205440) }, { argument := 5459623431230971934622613504, coefficient := (-5459623431230971934622613504) }, { argument := 19415437695713435446946037760, coefficient := (-19415437695713435446946037760) }, { argument := 5458351620796328201825550336, coefficient := (-5458351620796328201825550336) }, { argument := 218160412161242110464360448, coefficient := (-218160412161242110464360448) }, { argument := 776632167583955024275832832, coefficient := (-776632167583955024275832832) }, { argument := 218085860615593933009846272, coefficient := (-218085860615593933009846272) }, { argument := 1901475900342344102245054808064, coefficient := 1901475900342344102245054808064 }, { argument := 142566015160854674528941375488, coefficient := 142566015160854674528941375488 }, { argument := 507188582678616598668441026560, coefficient := 507188582678616598668441026560 }, { argument := 142527027303172102738057101312, coefficient := 142527027303172102738057101312 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 29699661721006663456425771008, coefficient := 29699661721006663456425771008 }, { argument := 1079494131797312810149377736704, coefficient := 1079494131797312810149377736704 }, { argument := 1079495397391530219214295007232, coefficient := 1079495397391530219214295007232 }, { argument := 29699359489551759799132094464, coefficient := 29699359489551759799132094464 }, { argument := 2218388550399401452619230609408, coefficient := (-2218388550399401452619230609408) }, { argument := 2475445620854336542438588416, coefficient := 2475445620854336542438588416 }, { argument := 60718422071673304910393245696, coefficient := 60718422071673304910393245696 }, { argument := 665995175073912681180319186944, coefficient := 665995175073912681180319186944 }, { argument := 60666825495481471166788403200, coefficient := 60666825495481471166788403200 }, { argument := 2425756880721582135500079104, coefficient := 2425756880721582135500079104 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3
