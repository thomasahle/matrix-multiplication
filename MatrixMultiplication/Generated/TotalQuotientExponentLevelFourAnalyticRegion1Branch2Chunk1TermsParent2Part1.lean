import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2426535020230169755096089588924416)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    102237031, 20572386273, 359991114147, 359991290709, 20572209711, 2826531065,
    28216425, 9207465, 9821818825, 92965695, 2826530155, 186228405,
    83461215, 28216425, 9207465, 2826530155, 3668750703, 1408661345,
    1247671477, 58399074617, 15897749465, 1834375491, 58399074617, 1408661345,
    1408661345, 603712005, 1408661345, 15897749465, 603712005, 706632469,
    1247671477, 28190047663, 759727651829, 179059792779, 138950585235, 183741094551,
    5851627215, 179059792779, 101818313541, 183741094551, 2868467660793, 3510976329,
    379863830003, 179059792779, 5851627215, 3510976329, 5851627215, 90115059111,
    101818313541, 28190047663, 151245576205, 73718166375, 17449466405, 1824132499875,
    58033450125, 34898935695, 29800960875, 29800960875, 1008527254875, 54896506875,
    1824132499875, 1008527254875, 151245570435, 58033450125
  ]
def negativeCoefficients : Array ℕ := #[
    117871271607056857097568256, 23718346535220404990873960448, 830082993934908872189955538944, 830083401059162264978187091968, 23718142973093708596758183936, 6517536896555587178730618880,
    520501170650020034956492800, 21230968802829764583751680, 22647572275389707705542246400, 428728595824884923529953280, 6517534798238448794269122560, 429413465786266528839106560,
    384896918296462183744143360, 520501170650020034956492800, 21230968802829764583751680, 6517534798238448794269122560, 8459563161060375163626848256, 6496303829435619029685370880,
    5753869106071548283435614208, 269318195900316663202099232768, 73315428932201986192163471360, 8459563804390574734247460864, 269318195900316663202099232768, 6496303829435619029685370880,
    6496303829435619029685370880, 5568260425230530596873175040, 6496303829435619029685370880, 73315428932201986192163471360, 5568260425230530596873175040, 6517534154908249223648509952,
    5753869106071548283435614208, 32500912166564690329587417088, 875906347438117458912009519104, 825767542821419653548491145216, 160199117795138135903289999360, 847356236751391409196817711104,
    26985867412464694560408207360, 825767542821419653548491145216, 469554092976885685351102808064, 847356236751391409196817711104, 13228472205590193273512103247872, 518128654319322135559837581312,
    875906356865556602082197241856, 825767542821419653548491145216, 26985867412464694560408207360, 518128654319322135559837581312, 26985867412464694560408207360, 831164716303912592460572786688,
    469554092976885685351102808064, 32500912166564690329587417088, 174374277283398132873381806080, 169982518587845748681867264000, 160942920497913832325502730240, 4206163172716268206744928256000,
    133816025271282823430406144000, 160942933802627995488516833280, 137432674602939115955552256000, 137432674602939115955552256000, 2325505520254996093668950016000, 126582726607970238380113920000,
    4206163172716268206744928256000, 2325505520254996093668950016000, 174374270631041051291874754560, 133816025271282823430406144000
  ]
def negativeScales : Array ℕ := #[
    26, 34, 38, 38, 34, 31,
    24, 23, 33, 26, 31, 27,
    26, 24, 23, 31, 31, 30,
    30, 35, 33, 30, 35, 30,
    30, 29, 30, 33, 29, 29,
    30, 34, 39, 37, 37, 37,
    32, 37, 36, 37, 41, 31,
    38, 37, 32, 31, 32, 36,
    36, 34, 37, 36, 34, 40,
    35, 35, 34, 34, 39, 35,
    40, 39, 37, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26607342604730956, 34259990096385057, 38389170339942963, 38389171047530037, 34259977714437163, 31396385407011850,
    24750031875564819, 23134372577395710, 33193343064558096, 26470195113941550, 31396384942536962, 27472497899810978,
    26314602587229761, 24750031875564819, 23134372577395710, 31396384942536962, 31772641729021803, 30391677670308471,
    30216590963750376, 35765226457742793, 33888103499951161, 30772641838735419, 35765226457742793, 30391677670308471,
    30391677670308471, 29169285248972019, 30391677670308471, 33888103499951161, 29169285248972019, 29396384800131994,
    30216590963750376, 34714466866156663, 39466691375772966, 37381650465560241, 37015780954685602, 37418883371759228,
    32446190717754989, 37381650465560241, 36567206118718536, 37418883371759228, 41383417391734429, 31709225123678539,
    38466691391300790, 37381650465560241, 32446190717754989, 31709225123678539, 32446190717754989, 36391049163562492,
    36567206118718536, 34714466866156663, 37138101989252721, 36101301135488022, 34022463869169269, 40730347665429069,
    35756165649696501, 35022463988432945, 34794639797832895, 34794639797832895, 39875387213928739, 35675995300796075,
    40730347665429069, 39875387213928739, 37138101934214082, 35756165649696501
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 18719220471 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 117871271607056857097568256, coefficient := (-117871271607056857097568256) }, { argument := 23718346535220404990873960448, coefficient := (-23718346535220404990873960448) }, { argument := 830082993934908872189955538944, coefficient := (-830082993934908872189955538944) }, { argument := 830083401059162264978187091968, coefficient := (-830083401059162264978187091968) }, { argument := 23718142973093708596758183936, coefficient := (-23718142973093708596758183936) }, { argument := 6517536896555587178730618880, coefficient := (-6517536896555587178730618880) }, { argument := 520501170650020034956492800, coefficient := (-520501170650020034956492800) }, { argument := 21230968802829764583751680, coefficient := (-21230968802829764583751680) }, { argument := 22647572275389707705542246400, coefficient := (-22647572275389707705542246400) }, { argument := 428728595824884923529953280, coefficient := (-428728595824884923529953280) }, { argument := 6517534798238448794269122560, coefficient := (-6517534798238448794269122560) }, { argument := 429413465786266528839106560, coefficient := (-429413465786266528839106560) }, { argument := 384896918296462183744143360, coefficient := (-384896918296462183744143360) }, { argument := 520501170650020034956492800, coefficient := (-520501170650020034956492800) }, { argument := 21230968802829764583751680, coefficient := (-21230968802829764583751680) }, { argument := 6517534798238448794269122560, coefficient := (-6517534798238448794269122560) }, { argument := 8459563161060375163626848256, coefficient := (-8459563161060375163626848256) }, { argument := 6496303829435619029685370880, coefficient := (-6496303829435619029685370880) }, { argument := 5753869106071548283435614208, coefficient := (-5753869106071548283435614208) }, { argument := 269318195900316663202099232768, coefficient := (-269318195900316663202099232768) }, { argument := 73315428932201986192163471360, coefficient := (-73315428932201986192163471360) }, { argument := 8459563804390574734247460864, coefficient := (-8459563804390574734247460864) }, { argument := 269318195900316663202099232768, coefficient := (-269318195900316663202099232768) }, { argument := 6496303829435619029685370880, coefficient := (-6496303829435619029685370880) }, { argument := 6496303829435619029685370880, coefficient := (-6496303829435619029685370880) }, { argument := 5568260425230530596873175040, coefficient := (-5568260425230530596873175040) }, { argument := 6496303829435619029685370880, coefficient := (-6496303829435619029685370880) }, { argument := 73315428932201986192163471360, coefficient := (-73315428932201986192163471360) }, { argument := 5568260425230530596873175040, coefficient := (-5568260425230530596873175040) }, { argument := 6517534154908249223648509952, coefficient := (-6517534154908249223648509952) }, { argument := 5753869106071548283435614208, coefficient := (-5753869106071548283435614208) }, { argument := 32500912166564690329587417088, coefficient := (-32500912166564690329587417088) }, { argument := 875906347438117458912009519104, coefficient := (-875906347438117458912009519104) }, { argument := 825767542821419653548491145216, coefficient := (-825767542821419653548491145216) }, { argument := 160199117795138135903289999360, coefficient := (-160199117795138135903289999360) }, { argument := 847356236751391409196817711104, coefficient := (-847356236751391409196817711104) }, { argument := 26985867412464694560408207360, coefficient := (-26985867412464694560408207360) }, { argument := 825767542821419653548491145216, coefficient := (-825767542821419653548491145216) }, { argument := 469554092976885685351102808064, coefficient := (-469554092976885685351102808064) }, { argument := 847356236751391409196817711104, coefficient := (-847356236751391409196817711104) }, { argument := 13228472205590193273512103247872, coefficient := (-13228472205590193273512103247872) }, { argument := 518128654319322135559837581312, coefficient := (-518128654319322135559837581312) }, { argument := 875906356865556602082197241856, coefficient := (-875906356865556602082197241856) }, { argument := 825767542821419653548491145216, coefficient := (-825767542821419653548491145216) }, { argument := 26985867412464694560408207360, coefficient := (-26985867412464694560408207360) }, { argument := 518128654319322135559837581312, coefficient := (-518128654319322135559837581312) }, { argument := 26985867412464694560408207360, coefficient := (-26985867412464694560408207360) }, { argument := 831164716303912592460572786688, coefficient := (-831164716303912592460572786688) }, { argument := 469554092976885685351102808064, coefficient := (-469554092976885685351102808064) }, { argument := 32500912166564690329587417088, coefficient := (-32500912166564690329587417088) }, { argument := 174374277283398132873381806080, coefficient := (-174374277283398132873381806080) }, { argument := 169982518587845748681867264000, coefficient := (-169982518587845748681867264000) }, { argument := 160942920497913832325502730240, coefficient := (-160942920497913832325502730240) }, { argument := 4206163172716268206744928256000, coefficient := (-4206163172716268206744928256000) }, { argument := 133816025271282823430406144000, coefficient := (-133816025271282823430406144000) }, { argument := 160942933802627995488516833280, coefficient := (-160942933802627995488516833280) }, { argument := 137432674602939115955552256000, coefficient := (-137432674602939115955552256000) }, { argument := 137432674602939115955552256000, coefficient := (-137432674602939115955552256000) }, { argument := 2325505520254996093668950016000, coefficient := (-2325505520254996093668950016000) }, { argument := 126582726607970238380113920000, coefficient := (-126582726607970238380113920000) }, { argument := 4206163172716268206744928256000, coefficient := (-4206163172716268206744928256000) }, { argument := 2325505520254996093668950016000, coefficient := (-2325505520254996093668950016000) }, { argument := 174374270631041051291874754560, coefficient := (-174374270631041051291874754560) }, { argument := 133816025271282823430406144000, coefficient := (-133816025271282823430406144000) }] }

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


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-518010851816383775496778926784512)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    54896506875, 73718166375, 52500097, 5504540483, 59333444625, 2752272341,
    52500097, 21110226437, 369402646543, 369402827721, 21110045259, 3668751639,
    2362536855, 770933079, 25749269325, 7783937217, 3668750703, 15592743243,
    6988135329, 2362536855, 770933079, 672300205, 11764415495, 11764421265,
    672294435, 176082725, 4816310135, 1408661345, 186228405, 15592743243,
    7796374443, 93111381, 52500097, 5504540483, 59333444625, 2752272341,
    52500097, 83461215, 6988135329, 3494068929, 41729343, 1776713809,
    186285238451, 2007968678625, 93142690277, 1776713809, 20572386273, 359991114147,
    359991290709, 20572209711, 96710705, 10139942995, 109298450625, 5069975365,
    96710705, 11698023567, 204700829613, 204700930011, 11697923169, 155958985,
    4265874691, 1247671477, 28216425, 2362536855
  ]
def negativeCoefficients : Array ℕ := #[
    126582726607970238380113920000, 169982518587845748681867264000, 121056981650490826208313344, 12692606191659320356756258816, 136813608501124074892689408000, 12692615873894116045057163264,
    121056981650490826208313344, 24338434026337278323968704512, 851784510116213679306032807936, 851784927884238402624675643392, 24338225142324916664647286784, 8459565319329431787644387328,
    43581112728891652258324807680, 1777650650783738447379038208, 59373772665411862048171622400, 35897074431955492518041223168, 8459563161060375163626848256, 35954418001335613113117966336,
    32227085991627774433129660416, 43581112728891652258324807680, 1777650650783738447379038208, 775109363896091666368430080, 27126895226631008895096586240, 27126908531345172058110689280,
    775102711539010084861378560, 6496305927752757414146867200, 22211310109989625123611607040, 6496303829435619029685370880, 429413465786266528839106560, 35954418001335613113117966336,
    35954431013207714105992937472, 429400453914165535964135424, 121056981650490826208313344, 12692606191659320356756258816, 136813608501124074892689408000, 12692615873894116045057163264,
    121056981650490826208313344, 384896918296462183744143360, 32227085991627774433129660416, 32227097654581715035993669632, 384885255342521580880134144, 2048411557928042138209091584,
    214772257400972183931428274176, 2315030270163757372526297088000, 214772421234576753078204104704, 2048411557928042138209091584, 23718346535220404990873960448, 830082993934908872189955538944,
    830083401059162264978187091968, 23718142973093708596758183936, 111499851520188918876078080, 11690558334423058223328133120, 126012534145772174243266560000, 11690567252270896357289492480,
    111499851520188918876078080, 13486902931791994994810683392, 472007976943379554774680600576, 472008208445405993811125993472, 13486787180778775476587986944, 5753870964581013709672939520,
    19672874668847953680913137664, 5753869106071548283435614208, 520501170650020034956492800, 43581112728891652258324807680
  ]
def negativeScales : Array ℕ := #[
    35, 36, 25, 32, 35, 31,
    25, 34, 38, 38, 34, 31,
    31, 29, 34, 32, 31, 33,
    32, 31, 29, 29, 33, 33,
    29, 27, 32, 30, 27, 33,
    32, 26, 25, 32, 35, 31,
    25, 26, 32, 31, 25, 30,
    37, 40, 36, 30, 34, 38,
    38, 34, 26, 33, 36, 32,
    26, 33, 37, 37, 33, 27,
    31, 30, 24, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35675995300796075, 36101301135488022, 25645816752557820, 32357974987155117, 35788126490801438, 31357976087678255,
    25645816752557820, 34297223002584033, 38426403246141953, 38426403953729027, 34297210620636138, 31772642097093255,
    31137689689187065, 29522030391243549, 34583812443069951, 32857852929799456, 31772641729021803, 33860155715758173,
    32702260401153377, 31137689689187065, 29522030391243549, 29324530348579768, 33453710592137722, 33453711299724797,
    29324517966631873, 27391678136301338, 32165281148039979, 30391677670308471, 27472497899810978, 33860155715758173,
    32860156237868159, 26472454183324965, 25645816752557820, 32357974987155117, 35788126490801438, 31357976087678255,
    25645816752557820, 26314602587229761, 32702260401153377, 31702260923263343, 25314558870743748, 30726564166556606,
    37438722401039508, 40868873906652351, 36438723501562646, 30726564166556606, 34259990096385057, 38389170339942963,
    38389171047530037, 34259977714437163, 26527172256040709, 33239330490656497, 36669481993831386, 32239331591179635,
    26527172256040709, 33445545749541173, 37574725993101800, 37574726700688875, 33445533367593278, 27216591429743242,
    31990194461713996, 30216590963750376, 24750031875564819, 31137689689187065
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 489898257 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 126582726607970238380113920000, coefficient := (-126582726607970238380113920000) }, { argument := 169982518587845748681867264000, coefficient := (-169982518587845748681867264000) }, { argument := 121056981650490826208313344, coefficient := (-121056981650490826208313344) }, { argument := 12692606191659320356756258816, coefficient := (-12692606191659320356756258816) }, { argument := 136813608501124074892689408000, coefficient := (-136813608501124074892689408000) }, { argument := 12692615873894116045057163264, coefficient := (-12692615873894116045057163264) }, { argument := 121056981650490826208313344, coefficient := (-121056981650490826208313344) }, { argument := 24338434026337278323968704512, coefficient := (-24338434026337278323968704512) }, { argument := 851784510116213679306032807936, coefficient := (-851784510116213679306032807936) }, { argument := 851784927884238402624675643392, coefficient := (-851784927884238402624675643392) }, { argument := 24338225142324916664647286784, coefficient := (-24338225142324916664647286784) }, { argument := 8459565319329431787644387328, coefficient := (-8459565319329431787644387328) }, { argument := 43581112728891652258324807680, coefficient := (-43581112728891652258324807680) }, { argument := 1777650650783738447379038208, coefficient := (-1777650650783738447379038208) }, { argument := 59373772665411862048171622400, coefficient := (-59373772665411862048171622400) }, { argument := 35897074431955492518041223168, coefficient := (-35897074431955492518041223168) }, { argument := 8459563161060375163626848256, coefficient := (-8459563161060375163626848256) }, { argument := 35954418001335613113117966336, coefficient := (-35954418001335613113117966336) }, { argument := 32227085991627774433129660416, coefficient := (-32227085991627774433129660416) }, { argument := 43581112728891652258324807680, coefficient := (-43581112728891652258324807680) }, { argument := 1777650650783738447379038208, coefficient := (-1777650650783738447379038208) }, { argument := 775109363896091666368430080, coefficient := (-775109363896091666368430080) }, { argument := 27126895226631008895096586240, coefficient := (-27126895226631008895096586240) }, { argument := 27126908531345172058110689280, coefficient := (-27126908531345172058110689280) }, { argument := 775102711539010084861378560, coefficient := (-775102711539010084861378560) }, { argument := 6496305927752757414146867200, coefficient := (-6496305927752757414146867200) }, { argument := 22211310109989625123611607040, coefficient := (-22211310109989625123611607040) }, { argument := 6496303829435619029685370880, coefficient := (-6496303829435619029685370880) }, { argument := 429413465786266528839106560, coefficient := (-429413465786266528839106560) }, { argument := 35954418001335613113117966336, coefficient := (-35954418001335613113117966336) }, { argument := 35954431013207714105992937472, coefficient := (-35954431013207714105992937472) }, { argument := 429400453914165535964135424, coefficient := (-429400453914165535964135424) }, { argument := 121056981650490826208313344, coefficient := (-121056981650490826208313344) }, { argument := 12692606191659320356756258816, coefficient := (-12692606191659320356756258816) }, { argument := 136813608501124074892689408000, coefficient := (-136813608501124074892689408000) }, { argument := 12692615873894116045057163264, coefficient := (-12692615873894116045057163264) }, { argument := 121056981650490826208313344, coefficient := (-121056981650490826208313344) }, { argument := 384896918296462183744143360, coefficient := (-384896918296462183744143360) }, { argument := 32227085991627774433129660416, coefficient := (-32227085991627774433129660416) }, { argument := 32227097654581715035993669632, coefficient := (-32227097654581715035993669632) }, { argument := 384885255342521580880134144, coefficient := (-384885255342521580880134144) }, { argument := 2048411557928042138209091584, coefficient := (-2048411557928042138209091584) }, { argument := 214772257400972183931428274176, coefficient := (-214772257400972183931428274176) }, { argument := 2315030270163757372526297088000, coefficient := (-2315030270163757372526297088000) }, { argument := 214772421234576753078204104704, coefficient := (-214772421234576753078204104704) }, { argument := 2048411557928042138209091584, coefficient := (-2048411557928042138209091584) }, { argument := 23718346535220404990873960448, coefficient := (-23718346535220404990873960448) }, { argument := 830082993934908872189955538944, coefficient := (-830082993934908872189955538944) }, { argument := 830083401059162264978187091968, coefficient := (-830083401059162264978187091968) }, { argument := 23718142973093708596758183936, coefficient := (-23718142973093708596758183936) }, { argument := 111499851520188918876078080, coefficient := (-111499851520188918876078080) }, { argument := 11690558334423058223328133120, coefficient := (-11690558334423058223328133120) }, { argument := 126012534145772174243266560000, coefficient := (-126012534145772174243266560000) }, { argument := 11690567252270896357289492480, coefficient := (-11690567252270896357289492480) }, { argument := 111499851520188918876078080, coefficient := (-111499851520188918876078080) }, { argument := 13486902931791994994810683392, coefficient := (-13486902931791994994810683392) }, { argument := 472007976943379554774680600576, coefficient := (-472007976943379554774680600576) }, { argument := 472008208445405993811125993472, coefficient := (-472008208445405993811125993472) }, { argument := 13486787180778775476587986944, coefficient := (-13486787180778775476587986944) }, { argument := 5753870964581013709672939520, coefficient := (-5753870964581013709672939520) }, { argument := 19672874668847953680913137664, coefficient := (-19672874668847953680913137664) }, { argument := 5753869106071548283435614208, coefficient := (-5753869106071548283435614208) }, { argument := 520501170650020034956492800, coefficient := (-520501170650020034956492800) }, { argument := 43581112728891652258324807680, coefficient := (-43581112728891652258324807680) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
