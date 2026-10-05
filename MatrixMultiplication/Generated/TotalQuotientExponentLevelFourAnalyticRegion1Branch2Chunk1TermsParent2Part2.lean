import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2674979222810757961152255448055808)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1181268855, 14107785, 3213558569, 336935820091, 3631831373625, 168468038557,
    3213558569, 21110226437, 369402646543, 369402827721, 21110045259, 1776713809,
    186285238451, 2007968678625, 93142690277, 1776713809, 329561560491, 5766916475649,
    5766919304103, 329558732037, 7299886685, 199670457311, 58399074617, 403380123,
    7058649297, 7058652759, 403376661, 1987219325, 54355500095, 15897749465,
    233797647, 2206735911, 10232624241, 75281908485, 10500143829, 334399485,
    10232624241, 5818551039, 10500143829, 163922627547, 200639691, 1103368287,
    10232624241, 334399485, 200639691, 334399485, 5149752069, 5818551039,
    233797647, 1108835899, 3419529603, 190922618033, 84615168687, 2691970113,
    190922710353, 1382363031, 1382363031, 46782075207, 2546458215, 84615168687,
    46782075207, 1108830129, 2691970113, 2546458215
  ]
def negativeCoefficients : Array ℕ := #[
    43581128500857835279991439360, 520485398683837013289861120, 3704980780513706075796537344, 388460552655257620392303394816, 4187216491758086818426257408000, 388460848982601498957933707264,
    3704980780513706075796537344, 24338434026337278323968704512, 851784510116213679306032807936, 851784927884238402624675643392, 24338225142324916664647286784, 2048411557928042138209091584,
    214772257400972183931428274176, 2315030270163757372526297088000, 214772421234576753078204104704, 2048411557928042138209091584, 379958610181864134853804425216, 13297604040094520560376346574848,
    13297610562065403342885859885056, 379955349196422743599047770112, 269318282890550028797917265920, 920817456274141315838869766144, 269318195900316663202099232768, 14882099786804959994273857536,
    520836388351315370785854455808, 520836643801827303515725234176, 14881972061548993629338468352, 73315452613209690816800358400, 250670499812740054966473850880, 73315428932201986192163471360,
    1078201339811121932311461888, 40707092588481298534735282176, 23594825072020431082390290432, 173588262400402319903261982720, 24211683243837958692387422208, 771072714771909512496414720,
    23594825072020431082390290432, 13416665237031225517437616128, 24211683243837958692387422208, 377979844781190043025742495744, 14804596123620662639931162624, 40707104818672619404168003584,
    23594825072020431082390290432, 771072714771909512496414720, 14804596123620662639931162624, 771072714771909512496414720, 23749039614974812984889573376, 13416665237031225517437616128,
    1078201339811121932311461888, 40908824097189305862028525568, 15769796859753656443692122112, 880475168184338780141316472832, 390218590380712817957743362048, 12414520932146495498225713152,
    880475593935192001357767770112, 12750048524907211592772354048, 12750048524907211592772354048, 215744242145140448793490096128, 11743465746625063309132431360, 390218590380712817957743362048,
    215744242145140448793490096128, 40908611221762695253802876928, 12414520932146495498225713152, 11743465746625063309132431360
  ]
def negativeScales : Array ℕ := #[
    30, 23, 31, 38, 41, 37,
    31, 34, 38, 38, 34, 30,
    37, 40, 36, 30, 38, 42,
    42, 38, 32, 37, 35, 28,
    32, 32, 28, 30, 35, 33,
    27, 31, 33, 36, 33, 28,
    33, 32, 33, 37, 27, 30,
    33, 28, 27, 28, 32, 32,
    27, 30, 31, 37, 36, 31,
    37, 30, 30, 35, 31, 36,
    35, 30, 31, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30137690211297030, 23749988159078591, 31581524620571668, 38293682855184749, 41723834358450490, 37293683955707887,
    31581524620571668, 34297223002584033, 38426403246141953, 38426403953729027, 34297210620636138, 30726564166556606,
    37438722401039508, 40868873906652351, 36438723501562646, 30726564166556606, 38261757022559245, 42390937266117151,
    42390937973704225, 38261744640611350, 32765226923735663, 37538829935162701, 35765226457742793, 28587564754417555,
    32716744998078269, 32716745705665345, 28587552372469659, 30888103965944057, 35661706974188096, 33888103499951161,
    27800685170040551, 31039266840791083, 33252457132467368, 36131584151421268, 33289690038666343, 28316997384662079,
    33252457132467368, 32438012785623474, 33289690038666343, 37254224058641556, 27580031790499094, 30039267274239718,
    33252457132467368, 28316997384662079, 27580031790499094, 28316997384662079, 32261855830469618, 32438012785623474,
    27800685170040551, 30046398725151661, 31671150732907146, 37474197068405114, 36300197262666562, 31326015246822293,
    37474197766015357, 30364489394636930, 30364489394636930, 35445236808521329, 31245844898138310, 36300197262666562,
    35445236808521329, 30046391217844176, 31326015246822293, 31245844898138310
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
noncomputable def negativeCeiling : ℝ := 4298970763 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 43581128500857835279991439360, coefficient := (-43581128500857835279991439360) }, { argument := 520485398683837013289861120, coefficient := (-520485398683837013289861120) }, { argument := 3704980780513706075796537344, coefficient := (-3704980780513706075796537344) }, { argument := 388460552655257620392303394816, coefficient := (-388460552655257620392303394816) }, { argument := 4187216491758086818426257408000, coefficient := (-4187216491758086818426257408000) }, { argument := 388460848982601498957933707264, coefficient := (-388460848982601498957933707264) }, { argument := 3704980780513706075796537344, coefficient := (-3704980780513706075796537344) }, { argument := 24338434026337278323968704512, coefficient := (-24338434026337278323968704512) }, { argument := 851784510116213679306032807936, coefficient := (-851784510116213679306032807936) }, { argument := 851784927884238402624675643392, coefficient := (-851784927884238402624675643392) }, { argument := 24338225142324916664647286784, coefficient := (-24338225142324916664647286784) }, { argument := 2048411557928042138209091584, coefficient := (-2048411557928042138209091584) }, { argument := 214772257400972183931428274176, coefficient := (-214772257400972183931428274176) }, { argument := 2315030270163757372526297088000, coefficient := (-2315030270163757372526297088000) }, { argument := 214772421234576753078204104704, coefficient := (-214772421234576753078204104704) }, { argument := 2048411557928042138209091584, coefficient := (-2048411557928042138209091584) }, { argument := 379958610181864134853804425216, coefficient := (-379958610181864134853804425216) }, { argument := 13297604040094520560376346574848, coefficient := (-13297604040094520560376346574848) }, { argument := 13297610562065403342885859885056, coefficient := (-13297610562065403342885859885056) }, { argument := 379955349196422743599047770112, coefficient := (-379955349196422743599047770112) }, { argument := 269318282890550028797917265920, coefficient := (-269318282890550028797917265920) }, { argument := 920817456274141315838869766144, coefficient := (-920817456274141315838869766144) }, { argument := 269318195900316663202099232768, coefficient := (-269318195900316663202099232768) }, { argument := 14882099786804959994273857536, coefficient := (-14882099786804959994273857536) }, { argument := 520836388351315370785854455808, coefficient := (-520836388351315370785854455808) }, { argument := 520836643801827303515725234176, coefficient := (-520836643801827303515725234176) }, { argument := 14881972061548993629338468352, coefficient := (-14881972061548993629338468352) }, { argument := 73315452613209690816800358400, coefficient := (-73315452613209690816800358400) }, { argument := 250670499812740054966473850880, coefficient := (-250670499812740054966473850880) }, { argument := 73315428932201986192163471360, coefficient := (-73315428932201986192163471360) }, { argument := 1078201339811121932311461888, coefficient := (-1078201339811121932311461888) }, { argument := 40707092588481298534735282176, coefficient := (-40707092588481298534735282176) }, { argument := 23594825072020431082390290432, coefficient := (-23594825072020431082390290432) }, { argument := 173588262400402319903261982720, coefficient := (-173588262400402319903261982720) }, { argument := 24211683243837958692387422208, coefficient := (-24211683243837958692387422208) }, { argument := 771072714771909512496414720, coefficient := (-771072714771909512496414720) }, { argument := 23594825072020431082390290432, coefficient := (-23594825072020431082390290432) }, { argument := 13416665237031225517437616128, coefficient := (-13416665237031225517437616128) }, { argument := 24211683243837958692387422208, coefficient := (-24211683243837958692387422208) }, { argument := 377979844781190043025742495744, coefficient := (-377979844781190043025742495744) }, { argument := 14804596123620662639931162624, coefficient := (-14804596123620662639931162624) }, { argument := 40707104818672619404168003584, coefficient := (-40707104818672619404168003584) }, { argument := 23594825072020431082390290432, coefficient := (-23594825072020431082390290432) }, { argument := 771072714771909512496414720, coefficient := (-771072714771909512496414720) }, { argument := 14804596123620662639931162624, coefficient := (-14804596123620662639931162624) }, { argument := 771072714771909512496414720, coefficient := (-771072714771909512496414720) }, { argument := 23749039614974812984889573376, coefficient := (-23749039614974812984889573376) }, { argument := 13416665237031225517437616128, coefficient := (-13416665237031225517437616128) }, { argument := 1078201339811121932311461888, coefficient := (-1078201339811121932311461888) }, { argument := 40908824097189305862028525568, coefficient := (-40908824097189305862028525568) }, { argument := 15769796859753656443692122112, coefficient := (-15769796859753656443692122112) }, { argument := 880475168184338780141316472832, coefficient := (-880475168184338780141316472832) }, { argument := 390218590380712817957743362048, coefficient := (-390218590380712817957743362048) }, { argument := 12414520932146495498225713152, coefficient := (-12414520932146495498225713152) }, { argument := 880475593935192001357767770112, coefficient := (-880475593935192001357767770112) }, { argument := 12750048524907211592772354048, coefficient := (-12750048524907211592772354048) }, { argument := 12750048524907211592772354048, coefficient := (-12750048524907211592772354048) }, { argument := 215744242145140448793490096128, coefficient := (-215744242145140448793490096128) }, { argument := 11743465746625063309132431360, coefficient := (-11743465746625063309132431360) }, { argument := 390218590380712817957743362048, coefficient := (-390218590380712817957743362048) }, { argument := 215744242145140448793490096128, coefficient := (-215744242145140448793490096128) }, { argument := 40908611221762695253802876928, coefficient := (-40908611221762695253802876928) }, { argument := 12414520932146495498225713152, coefficient := (-12414520932146495498225713152) }, { argument := 11743465746625063309132431360, coefficient := (-11743465746625063309132431360) }] }

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

end TermShard4


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-436435127078615841996972016795648)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3419529603, 1834375959, 1181268855, 385466679, 12874637529, 3891970017,
    1834375491, 7796374443, 3494068929, 1181268855, 385466679, 20572386273,
    359991114147, 359991290709, 20572209711, 7299886685, 199670457311, 58399074617,
    176082725, 4816310135, 1408661345, 9207465, 770933079, 385466679,
    4603593, 102237031, 10719368309, 115544076375, 5359688243, 102237031,
    672300205, 11764415495, 11764421265, 672294435, 96710705, 10139942995,
    109298450625, 5069975365, 96710705, 403380123, 7058649297, 7058652759,
    403376661, 176082725, 4816310135, 1408661345, 672300205, 11764415495,
    11764421265, 672294435, 75464025, 2064132915, 603712005, 129868661,
    13616494879, 146772205125, 6808252633, 129868661, 10353423157, 181171998623,
    181172087481, 10353334299, 176082725, 4816310135
  ]
def negativeCoefficients : Array ℕ := #[
    15769796859753656443692122112, 8459565962659631358264999936, 43581128500857835279991439360, 1777651294113938017999650816, 59373785884809833870279049216, 35897087423075006427992948736,
    8459563804390574734247460864, 35954431013207714105992937472, 32227097654581715035993669632, 43581128500857835279991439360, 1777651294113938017999650816, 23718346535220404990873960448,
    830082993934908872189955538944, 830083401059162264978187091968, 23718142973093708596758183936, 269318282890550028797917265920, 920817456274141315838869766144, 269318195900316663202099232768,
    6496305927752757414146867200, 22211310109989625123611607040, 6496303829435619029685370880, 21230968802829764583751680, 1777650650783738447379038208, 1777651294113938017999650816,
    21230325472630193963139072, 117871271607056857097568256, 12358590239247232978946883584, 133213250382673441342881792000, 12358599666686376149134606336, 117871271607056857097568256,
    775109363896091666368430080, 27126895226631008895096586240, 27126908531345172058110689280, 775102711539010084861378560, 111499851520188918876078080, 11690558334423058223328133120,
    126012534145772174243266560000, 11690567252270896357289492480, 111499851520188918876078080, 14882099786804959994273857536, 520836388351315370785854455808, 520836643801827303515725234176,
    14881972061548993629338468352, 6496305927752757414146867200, 22211310109989625123611607040, 6496303829435619029685370880, 775109363896091666368430080, 27126895226631008895096586240,
    27126908531345172058110689280, 775102711539010084861378560, 5568262223788077783554457600, 19038265808562535820238520320, 5568260425230530596873175040, 149728372041396548205019136,
    15698749763368106757040635904, 169216831567179776840957952000, 15698761738763775108360175616, 149728372041396548205019136, 23873368407999623324147646464, 835508372980235073968974856192,
    835508782765431299389809229824, 23873163515401510613730459648, 6496305927752757414146867200, 22211310109989625123611607040
  ]
def negativeScales : Array ℕ := #[
    31, 30, 30, 28, 33, 31,
    30, 32, 31, 30, 28, 34,
    38, 38, 34, 32, 37, 35,
    27, 32, 30, 23, 29, 28,
    22, 26, 33, 36, 32, 26,
    29, 33, 33, 29, 26, 33,
    36, 32, 26, 28, 32, 32,
    28, 27, 32, 30, 29, 33,
    33, 29, 26, 30, 29, 26,
    33, 37, 32, 26, 33, 37,
    37, 33, 27, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31671150732907146, 30772642206806842, 30137690211297030, 28522030913353515, 33583812764281775, 31857853451909441,
    30772641838735419, 32860156237868159, 31702260923263343, 30137690211297030, 28522030913353515, 34259990096385057,
    38389170339942963, 38389171047530037, 34259977714437163, 32765226923735663, 37538829935162701, 35765226457742793,
    27391678136301338, 32165281148039979, 30391677670308471, 23134372577395710, 29522030391243549, 28522030913353515,
    22134328860909696, 26607342604730956, 33319500839340481, 36749652342703838, 32319501939863619, 26607342604730956,
    29324530348579768, 33453710592137722, 33453711299724797, 29324517966631873, 26527172256040709, 33239330490656497,
    36669481993831386, 32239331591179635, 26527172256040709, 28587564754417555, 32716744998078269, 32716745705665345,
    28587552372469659, 27391678136301338, 32165281148039979, 30391677670308471, 29324530348579768, 33453710592137722,
    33453711299724797, 29324517966631873, 26169285714964885, 30942888735943444, 29169285248972019, 26952478101641564,
    33664636325419953, 37094787828529347, 32664637425943092, 26952478101641564, 33269388794387307, 37398569037945214,
    37398569745532289, 33269376412439412, 27391678136301338, 32165281148039979
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
noncomputable def negativeCeiling : ℝ := 3041870593 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 15769796859753656443692122112, coefficient := (-15769796859753656443692122112) }, { argument := 8459565962659631358264999936, coefficient := (-8459565962659631358264999936) }, { argument := 43581128500857835279991439360, coefficient := (-43581128500857835279991439360) }, { argument := 1777651294113938017999650816, coefficient := (-1777651294113938017999650816) }, { argument := 59373785884809833870279049216, coefficient := (-59373785884809833870279049216) }, { argument := 35897087423075006427992948736, coefficient := (-35897087423075006427992948736) }, { argument := 8459563804390574734247460864, coefficient := (-8459563804390574734247460864) }, { argument := 35954431013207714105992937472, coefficient := (-35954431013207714105992937472) }, { argument := 32227097654581715035993669632, coefficient := (-32227097654581715035993669632) }, { argument := 43581128500857835279991439360, coefficient := (-43581128500857835279991439360) }, { argument := 1777651294113938017999650816, coefficient := (-1777651294113938017999650816) }, { argument := 23718346535220404990873960448, coefficient := (-23718346535220404990873960448) }, { argument := 830082993934908872189955538944, coefficient := (-830082993934908872189955538944) }, { argument := 830083401059162264978187091968, coefficient := (-830083401059162264978187091968) }, { argument := 23718142973093708596758183936, coefficient := (-23718142973093708596758183936) }, { argument := 269318282890550028797917265920, coefficient := (-269318282890550028797917265920) }, { argument := 920817456274141315838869766144, coefficient := (-920817456274141315838869766144) }, { argument := 269318195900316663202099232768, coefficient := (-269318195900316663202099232768) }, { argument := 6496305927752757414146867200, coefficient := (-6496305927752757414146867200) }, { argument := 22211310109989625123611607040, coefficient := (-22211310109989625123611607040) }, { argument := 6496303829435619029685370880, coefficient := (-6496303829435619029685370880) }, { argument := 21230968802829764583751680, coefficient := (-21230968802829764583751680) }, { argument := 1777650650783738447379038208, coefficient := (-1777650650783738447379038208) }, { argument := 1777651294113938017999650816, coefficient := (-1777651294113938017999650816) }, { argument := 21230325472630193963139072, coefficient := (-21230325472630193963139072) }, { argument := 117871271607056857097568256, coefficient := (-117871271607056857097568256) }, { argument := 12358590239247232978946883584, coefficient := (-12358590239247232978946883584) }, { argument := 133213250382673441342881792000, coefficient := (-133213250382673441342881792000) }, { argument := 12358599666686376149134606336, coefficient := (-12358599666686376149134606336) }, { argument := 117871271607056857097568256, coefficient := (-117871271607056857097568256) }, { argument := 775109363896091666368430080, coefficient := (-775109363896091666368430080) }, { argument := 27126895226631008895096586240, coefficient := (-27126895226631008895096586240) }, { argument := 27126908531345172058110689280, coefficient := (-27126908531345172058110689280) }, { argument := 775102711539010084861378560, coefficient := (-775102711539010084861378560) }, { argument := 111499851520188918876078080, coefficient := (-111499851520188918876078080) }, { argument := 11690558334423058223328133120, coefficient := (-11690558334423058223328133120) }, { argument := 126012534145772174243266560000, coefficient := (-126012534145772174243266560000) }, { argument := 11690567252270896357289492480, coefficient := (-11690567252270896357289492480) }, { argument := 111499851520188918876078080, coefficient := (-111499851520188918876078080) }, { argument := 14882099786804959994273857536, coefficient := (-14882099786804959994273857536) }, { argument := 520836388351315370785854455808, coefficient := (-520836388351315370785854455808) }, { argument := 520836643801827303515725234176, coefficient := (-520836643801827303515725234176) }, { argument := 14881972061548993629338468352, coefficient := (-14881972061548993629338468352) }, { argument := 6496305927752757414146867200, coefficient := (-6496305927752757414146867200) }, { argument := 22211310109989625123611607040, coefficient := (-22211310109989625123611607040) }, { argument := 6496303829435619029685370880, coefficient := (-6496303829435619029685370880) }, { argument := 775109363896091666368430080, coefficient := (-775109363896091666368430080) }, { argument := 27126895226631008895096586240, coefficient := (-27126895226631008895096586240) }, { argument := 27126908531345172058110689280, coefficient := (-27126908531345172058110689280) }, { argument := 775102711539010084861378560, coefficient := (-775102711539010084861378560) }, { argument := 5568262223788077783554457600, coefficient := (-5568262223788077783554457600) }, { argument := 19038265808562535820238520320, coefficient := (-19038265808562535820238520320) }, { argument := 5568260425230530596873175040, coefficient := (-5568260425230530596873175040) }, { argument := 149728372041396548205019136, coefficient := (-149728372041396548205019136) }, { argument := 15698749763368106757040635904, coefficient := (-15698749763368106757040635904) }, { argument := 169216831567179776840957952000, coefficient := (-169216831567179776840957952000) }, { argument := 15698761738763775108360175616, coefficient := (-15698761738763775108360175616) }, { argument := 149728372041396548205019136, coefficient := (-149728372041396548205019136) }, { argument := 23873368407999623324147646464, coefficient := (-23873368407999623324147646464) }, { argument := 835508372980235073968974856192, coefficient := (-835508372980235073968974856192) }, { argument := 835508782765431299389809229824, coefficient := (-835508782765431299389809229824) }, { argument := 23873163515401510613730459648, coefficient := (-23873163515401510613730459648) }, { argument := 6496305927752757414146867200, coefficient := (-6496305927752757414146867200) }, { argument := 22211310109989625123611607040, coefficient := (-22211310109989625123611607040) }] }

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

end TermShard5


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
