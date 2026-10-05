import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 5, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 2327277234566466616019081039446016
def positiveArguments : Array ℕ := #[
    213, 1, 1547943455, 13743, 1547674081, 6939,
    239195209, 8265, 2697, 1726289737, 27231, 478390309,
    54549, 24447, 8265, 2697, 42288055, 1175,
    407305729, 29075
  ]
def positiveCoefficients : Array ℕ := #[
    33751197231076607814849722843136, 2535301200456458802993406410752, 7309956289269436926712799559680, 531656561246843159935583256576, 7308684206520480398903005413376, 536879120787578357970313936896,
    4518269751378398826583457529856, 1278946803086708496505157713920, 52167566968010478146920906752, 16304345587461309682469153275904, 1053448287805630945805564116992, 4518268721902505561000800944128,
    1055131112546534509616755113984, 945747504387802861889340309504, 1278946803086708496505157713920, 52167566968010478146920906752, 199699693557748114627263201280, 90911221635020113937904435200,
    3846893845820773711471620128768, 2249569165138901968293252300800
  ]
def positiveScales : Array ℕ := #[
    7, 0, 30, 13, 30, 12,
    27, 13, 11, 30, 14, 28,
    15, 14, 13, 11, 25, 10,
    28, 14
  ]
def negativeArguments : Array ℕ := #[
    475, 2405425473, 4076871359, 2405425473, 16075, 16075,
    459, 875, 875, 261, 813222135, 1378301705,
    813222135, 29075, 29075, 471, 16075, 16075,
    7353, 9, 164136874788925, 802576439, 164105930602435, 405230147,
    8615985, 459, 265367223, 449761609, 265367223, 925,
    925, 15, 875, 875, 9, 15,
    1175, 1175, 231, 261, 255641, 1,
    99, 49
  ]
def negativeCoefficients : Array ℕ := #[
    18375672458142363455533875200, 88744536177625490121069428736, 300820010323637823472010264576, 88744536177625490121069428736, 310935720804882623734428467200, 310935720804882623734428467200,
    17756702438499673318084313088, 16924961474604808445886464000, 16924961474604808445886464000, 10096948445421382867145981952, 120010404795365431480449761280, 406802860935880330673892884480,
    120010404795365431480449761280, 562392291284725492073313075200, 562392291284725492073313075200, 18220929953231690921171484672, 310935720804882623734428467200, 310935720804882623734428467200,
    284455409652043786291664388096, 11141460353568422474092118016, 46200423008572524330798284800, 3701230542455541364063993856, 46191712994400921384764047360, 3737588406330350218327883776,
    81375677561815240233053061120, 17756702438499673318084313088, 4895161248232011020913082368, 16593274590805645066961420288, 4895161248232011020913082368, 17892102130296511785651404800,
    17892102130296511785651404800, 580284393415022003858964480, 16924961474604808445886464000, 16924961474604808445886464000, 11141460353568422474092118016, 580284393415022003858964480,
    22727805408755028484476108800, 22727805408755028484476108800, 17872759317182677718856105984, 10096948445421382867145981952, 1207230490047278972074459136, 2535301200456458802993406410752,
    15687176177824338843521702166528, 31057439705591620336669228531712
  ]
def negativeScales : Array ℕ := #[
    8, 31, 31, 31, 13, 13,
    8, 9, 9, 8, 29, 30,
    29, 14, 14, 8, 13, 13,
    12, 3, 47, 29, 47, 28,
    23, 8, 27, 28, 27, 9,
    9, 3, 9, 9, 3, 3,
    10, 10, 7, 8, 17, 0,
    6, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7734709620215885, 0, 30527705626062185, 13746409348226269, 30527454545603824, 12760512051339829,
    27833613252147202, 13012799104179676, 11397139806235602, 30685027477858485, 14732962342771775, 28833612923432890,
    15735265128640690, 14577369816069468, 13012799104179676, 11397139806235602, 25333746870679357, 10198445041452361,
    28601536865955845, 14827491571178588
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8891783706984896, 31163644955256768, 31924815295713265, 31163644955256768, 13972531132277330, 13972531132277330,
    8842350344909532, 9773139207089529, 9773139207089529, 8027905996569885, 29599074243372301, 30360244577053537,
    29599074243372301, 14827491572368013, 14827491572368013, 8879583252627603, 13972531132277330, 13972531132277330,
    12844117271135484, 3169925001442313, 47221892717785661, 29580063563068537, 47221620705581327, 28594166266188302,
    23038584307548397, 8842350344909532, 27983414963552446, 28744585279309155, 27983414963552446, 9853309557248504,
    9853309557248504, 3906890600547867, 9773139207089529, 9773139207089529, 3169925001442313, 3906890600547867,
    10198445041452363, 10198445041452363, 7851749043206919, 8027905996569885, 17963759723507909, 0,
    6629356620092098, 5614709844123661
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 44
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
noncomputable def positiveFloor : ℝ := 4110841459 / 200000000000
noncomputable def negativeCeiling : ℝ := 4338098387 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 18375672458142363455533875200, coefficient := (-18375672458142363455533875200) }, { argument := 88744536177625490121069428736, coefficient := (-88744536177625490121069428736) }, { argument := 300820010323637823472010264576, coefficient := (-300820010323637823472010264576) }, { argument := 88744536177625490121069428736, coefficient := (-88744536177625490121069428736) }, { argument := 310935720804882623734428467200, coefficient := (-310935720804882623734428467200) }, { argument := 310935720804882623734428467200, coefficient := (-310935720804882623734428467200) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 10096948445421382867145981952, coefficient := (-10096948445421382867145981952) }, { argument := 120010404795365431480449761280, coefficient := (-120010404795365431480449761280) }, { argument := 406802860935880330673892884480, coefficient := (-406802860935880330673892884480) }, { argument := 120010404795365431480449761280, coefficient := (-120010404795365431480449761280) }, { argument := 562392291284725492073313075200, coefficient := (-562392291284725492073313075200) }, { argument := 562392291284725492073313075200, coefficient := (-562392291284725492073313075200) }, { argument := 18220929953231690921171484672, coefficient := (-18220929953231690921171484672) }, { argument := 310935720804882623734428467200, coefficient := (-310935720804882623734428467200) }, { argument := 310935720804882623734428467200, coefficient := (-310935720804882623734428467200) }, { argument := 284455409652043786291664388096, coefficient := (-284455409652043786291664388096) }, { argument := 11141460353568422474092118016, coefficient := (-11141460353568422474092118016) }, { argument := 46200423008572524330798284800, coefficient := (-46200423008572524330798284800) }, { argument := 3701230542455541364063993856, coefficient := (-3701230542455541364063993856) }, { argument := 46191712994400921384764047360, coefficient := (-46191712994400921384764047360) }, { argument := 3737588406330350218327883776, coefficient := (-3737588406330350218327883776) }, { argument := 81375677561815240233053061120, coefficient := (-81375677561815240233053061120) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 4895161248232011020913082368, coefficient := (-4895161248232011020913082368) }, { argument := 16593274590805645066961420288, coefficient := (-16593274590805645066961420288) }, { argument := 4895161248232011020913082368, coefficient := (-4895161248232011020913082368) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 11141460353568422474092118016, coefficient := (-11141460353568422474092118016) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 22727805408755028484476108800, coefficient := (-22727805408755028484476108800) }, { argument := 22727805408755028484476108800, coefficient := (-22727805408755028484476108800) }, { argument := 17872759317182677718856105984, coefficient := (-17872759317182677718856105984) }, { argument := 10096948445421382867145981952, coefficient := (-10096948445421382867145981952) }, { argument := 1207230490047278972074459136, coefficient := (-1207230490047278972074459136) }, { argument := 33751197231076607814849722843136, coefficient := 33751197231076607814849722843136 }, { argument := 2535301200456458802993406410752, coefficient := 2535301200456458802993406410752 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 7309956289269436926712799559680, coefficient := 7309956289269436926712799559680 }, { argument := 531656561246843159935583256576, coefficient := 531656561246843159935583256576 }, { argument := 7308684206520480398903005413376, coefficient := 7308684206520480398903005413376 }, { argument := 536879120787578357970313936896, coefficient := 536879120787578357970313936896 }, { argument := 15687176177824338843521702166528, coefficient := (-15687176177824338843521702166528) }, { argument := 4518269751378398826583457529856, coefficient := 4518269751378398826583457529856 }, { argument := 1278946803086708496505157713920, coefficient := 1278946803086708496505157713920 }, { argument := 52167566968010478146920906752, coefficient := 52167566968010478146920906752 }, { argument := 16304345587461309682469153275904, coefficient := 16304345587461309682469153275904 }, { argument := 1053448287805630945805564116992, coefficient := 1053448287805630945805564116992 }, { argument := 4518268721902505561000800944128, coefficient := 4518268721902505561000800944128 }, { argument := 1055131112546534509616755113984, coefficient := 1055131112546534509616755113984 }, { argument := 945747504387802861889340309504, coefficient := 945747504387802861889340309504 }, { argument := 1278946803086708496505157713920, coefficient := 1278946803086708496505157713920 }, { argument := 52167566968010478146920906752, coefficient := 52167566968010478146920906752 }, { argument := 31057439705591620336669228531712, coefficient := (-31057439705591620336669228531712) }, { argument := 199699693557748114627263201280, coefficient := 199699693557748114627263201280 }, { argument := 90911221635020113937904435200, coefficient := 90911221635020113937904435200 }, { argument := 3846893845820773711471620128768, coefficient := 3846893845820773711471620128768 }, { argument := 2249569165138901968293252300800, coefficient := 2249569165138901968293252300800 }] }

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

end TermShard2


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-836977917794213300787027120226304)
def positiveArguments : Array ℕ := #[
    925, 814611823, 475, 475, 16075, 875,
    29075, 16075, 5285979, 925, 875, 1175,
    255641, 17231965, 459, 141079055, 471, 15,
    459, 261, 471, 7353, 9, 8615985,
    459, 15, 9, 15, 231, 261,
    255641
  ]
def positiveCoefficients : Array ℕ := #[
    71568408521186047142605619200, 3846895569484539958892123127808, 73502689832569453822135500800, 73502689832569453822135500800, 1243742883219530494937713868800, 67699845898419233783545856000,
    2249569165138901968293252300800, 1243742883219530494937713868800, 199698640470022434696380547072, 71568408521186047142605619200, 67699845898419233783545856000, 90911221635020113937904435200,
    2414460980094557944148918272, 162751307899965651769653985280, 35513404876999346636168626176, 1332454001533846469867009474560, 36441859906463381842342969344, 1160568786830044007717928960,
    35513404876999346636168626176, 20193896890842765734291963904, 36441859906463381842342969344, 568910819304087572583328776192, 22282920707136844948184236032, 162751355123630480466106122240,
    35513404876999346636168626176, 1160568786830044007717928960, 22282920707136844948184236032, 1160568786830044007717928960, 35745518634365355437712211968, 20193896890842765734291963904,
    2414460980094557944148918272
  ]
def positiveScales : Array ℕ := #[
    9, 29, 8, 8, 13, 9,
    14, 13, 22, 9, 9, 10,
    17, 24, 8, 27, 8, 3,
    8, 8, 8, 12, 3, 23,
    8, 3, 3, 3, 7, 8,
    17
  ]
def negativeArguments : Array ℕ := #[
    99, 1
  ]
def negativeCoefficients : Array ℕ := #[
    15687176177824338843521702166528, 2535301200456458802993406410752
  ]
def negativeScales : Array ℕ := #[
    6, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9853309555289512, 29601537512378833, 8891783702985444, 8891783702985444, 13972531116166486, 9773139206696762,
    14827491571178588, 13972531116166486, 22333739262813675, 9853309555289512, 9773139206696762, 10198445041452361,
    17963759709571778, 24038583888938321, 8842350343321225, 27071928576299916, 8879583249426338, 3906890595303263,
    8842350343321225, 8027905996569884, 8879583249426338, 12844117269492213, 3169925001442312, 23038584307548396,
    8842350343321225, 3906890595303263, 3169925001442312, 3906890595303263, 7851749041305231, 8027905996569884,
    17963759709571778
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6629356620092098, 0
  ]

abbrev PositiveTerm := Fin 31
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
noncomputable def positiveFloor : ℝ := 29477659 / 10000000000
noncomputable def negativeCeiling : ℝ := 250360987 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 3846895569484539958892123127808, coefficient := 3846895569484539958892123127808 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }, { argument := 1243742883219530494937713868800, coefficient := 1243742883219530494937713868800 }, { argument := 67699845898419233783545856000, coefficient := 67699845898419233783545856000 }, { argument := 2249569165138901968293252300800, coefficient := 2249569165138901968293252300800 }, { argument := 1243742883219530494937713868800, coefficient := 1243742883219530494937713868800 }, { argument := 199698640470022434696380547072, coefficient := 199698640470022434696380547072 }, { argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 67699845898419233783545856000, coefficient := 67699845898419233783545856000 }, { argument := 90911221635020113937904435200, coefficient := 90911221635020113937904435200 }, { argument := 15687176177824338843521702166528, coefficient := (-15687176177824338843521702166528) }, { argument := 2414460980094557944148918272, coefficient := 2414460980094557944148918272 }, { argument := 162751307899965651769653985280, coefficient := 162751307899965651769653985280 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 1332454001533846469867009474560, coefficient := 1332454001533846469867009474560 }, { argument := 36441859906463381842342969344, coefficient := 36441859906463381842342969344 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 20193896890842765734291963904, coefficient := 20193896890842765734291963904 }, { argument := 36441859906463381842342969344, coefficient := 36441859906463381842342969344 }, { argument := 568910819304087572583328776192, coefficient := 568910819304087572583328776192 }, { argument := 22282920707136844948184236032, coefficient := 22282920707136844948184236032 }, { argument := 162751355123630480466106122240, coefficient := 162751355123630480466106122240 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 22282920707136844948184236032, coefficient := 22282920707136844948184236032 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 35745518634365355437712211968, coefficient := 35745518634365355437712211968 }, { argument := 20193896890842765734291963904, coefficient := 20193896890842765734291963904 }, { argument := 2414460980094557944148918272, coefficient := 2414460980094557944148918272 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }] }

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

end TermShard3


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5
