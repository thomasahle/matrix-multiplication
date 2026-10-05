import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-60261302024818183427207571963904)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    18411, 623067, 33915, 1126947, 623067, 4925556465,
    35853, 33915, 45543, 430076627, 729648437, 430076611,
    729167772149, 40366093153803, 61220635, 54223991, 2538032611, 690918595,
    20183050209387, 2538032611, 61220635, 61220635, 26237415, 61220635,
    690918595, 26237415, 364580253589, 54223991, 736517762683, 76439824335025,
    230030451, 768359915436715, 236044319, 7517335, 230030451, 130801629,
    236044319, 3684997617, 4510401, 38219925656535, 230030451, 7517335,
    4510401, 7517335, 115766959, 130801629, 736517762683, 14324593982991,
    4371, 250543603694637, 108159, 3441, 250543722393435, 1767,
    1767, 59799, 3255, 108159, 59799, 14324462824161,
    3441, 3255, 4371, 424731
  ]
def negativeCoefficients : Array ℕ := #[
    347773957264452152117428224, 5884701434764282468723851264, 320318118533048034844999680, 10643713481540996129278132224, 5884701434764282468723851264, 11357559941307564811804999680,
    338622011020650779693285376, 320318118533048034844999680, 430141473458664503934713856, 31734053881412973346766716928, 107677103848969497028681793536, 31734052700821352629355413504,
    410484963367601391416639488, 22724090260733740060074049536, 141165173234373194437099520, 125032010579016257930002432, 5852304753230728717949468672, 1593149812216497480075837440,
    22724094350548826117256511488, 5852304753230728717949468672, 141165173234373194437099520, 141165173234373194437099520, 120998719915177023803228160, 141165173234373194437099520,
    1593149812216497480075837440, 120998719915177023803228160, 410480873552515334234177536, 125032010579016257930002432, 414622640196363775530500096, 43031795548935595274063052800,
    2121656429378492700618129408, 432548178605901936416868270080, 2177124571323028457497034752, 69335177430669696098631680, 2121656429378492700618129408, 1206432087293652712116191232,
    2177124571323028457497034752, 33988103976514285027549249536, 1331235406668858165093728256, 43031810736224771422122147840, 2121656429378492700618129408, 69335177430669696098631680,
    1331235406668858165093728256, 69335177430669696098631680, 2135523464864626639837855744, 1206432087293652712116191232, 414622640196363775530500096, 4032014757751994794792452096,
    20641463896623219229065216, 141043510029903552261855903744, 510766436420697956668145664, 16249663067554449180327936, 141043576851386357527577886720, 16688843150461326185201664,
    16688843150461326185201664, 282392793309121914133807104, 15371302901740695170580480, 510766436420697956668145664, 282392793309121914133807104, 4031977839823375147902959616,
    16249663067554449180327936, 15371302901740695170580480, 20641463896623219229065216, 125358464914731705078644736
  ]
def negativeScales : Array ℕ := #[
    14, 19, 15, 20, 19, 32,
    15, 15, 15, 28, 29, 28,
    39, 45, 25, 25, 31, 29,
    44, 31, 25, 25, 24, 25,
    29, 24, 38, 25, 39, 46,
    27, 49, 27, 22, 27, 26,
    27, 31, 22, 45, 27, 22,
    22, 22, 26, 26, 39, 43,
    12, 47, 16, 11, 47, 10,
    10, 15, 11, 16, 15, 43,
    11, 11, 12, 18
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14168280368858667, 19249027782743029, 15049635872360048, 20103988236888300, 19249027782743029, 32197639576310709,
    15129806221044031, 15049635872360048, 15474941707092834, 28680018487665498, 29442626263684090, 28680018433993386,
    39407459842126117, 45198209195375561, 25867514675659074, 25692427966750701, 31241063460370056, 29363940499367778,
    44198209455027558, 31241063460370056, 25867514675659074, 25867514675659074, 24645122251930640, 25867514675659074,
    29363940499367778, 24645122251930640, 38407445467944689, 25692427966750701, 39421929363082765, 46119389696423562,
    27777249614579607, 49448775585441781, 27814482521240705, 22841789867850629, 27777249614579607, 26962805280251828,
    27814482521240705, 31779016540769046, 22104824272204778, 45119390205596434, 27777249614579607, 22841789867850629,
    22104824272204778, 22841789867850629, 26786648312669384, 26962805280251828, 39421929363082765, 43703559481355626,
    12093747662785669, 47832055036300584, 16722794192703879, 11748612176955137, 47832055719798898, 10787086325046961,
    10787086325046961, 15867833740861174, 11668441828086828, 16722794192703879, 15867833740861174, 43703546271692548,
    11748612176955137, 11668441828086828, 12093747662785669, 18696189885552550
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
noncomputable def negativeCeiling : ℝ := 591738219 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 347773957264452152117428224, coefficient := (-347773957264452152117428224) }, { argument := 5884701434764282468723851264, coefficient := (-5884701434764282468723851264) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 10643713481540996129278132224, coefficient := (-10643713481540996129278132224) }, { argument := 5884701434764282468723851264, coefficient := (-5884701434764282468723851264) }, { argument := 11357559941307564811804999680, coefficient := (-11357559941307564811804999680) }, { argument := 338622011020650779693285376, coefficient := (-338622011020650779693285376) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 430141473458664503934713856, coefficient := (-430141473458664503934713856) }, { argument := 31734053881412973346766716928, coefficient := (-31734053881412973346766716928) }, { argument := 107677103848969497028681793536, coefficient := (-107677103848969497028681793536) }, { argument := 31734052700821352629355413504, coefficient := (-31734052700821352629355413504) }, { argument := 410484963367601391416639488, coefficient := (-410484963367601391416639488) }, { argument := 22724090260733740060074049536, coefficient := (-22724090260733740060074049536) }, { argument := 141165173234373194437099520, coefficient := (-141165173234373194437099520) }, { argument := 125032010579016257930002432, coefficient := (-125032010579016257930002432) }, { argument := 5852304753230728717949468672, coefficient := (-5852304753230728717949468672) }, { argument := 1593149812216497480075837440, coefficient := (-1593149812216497480075837440) }, { argument := 22724094350548826117256511488, coefficient := (-22724094350548826117256511488) }, { argument := 5852304753230728717949468672, coefficient := (-5852304753230728717949468672) }, { argument := 141165173234373194437099520, coefficient := (-141165173234373194437099520) }, { argument := 141165173234373194437099520, coefficient := (-141165173234373194437099520) }, { argument := 120998719915177023803228160, coefficient := (-120998719915177023803228160) }, { argument := 141165173234373194437099520, coefficient := (-141165173234373194437099520) }, { argument := 1593149812216497480075837440, coefficient := (-1593149812216497480075837440) }, { argument := 120998719915177023803228160, coefficient := (-120998719915177023803228160) }, { argument := 410480873552515334234177536, coefficient := (-410480873552515334234177536) }, { argument := 125032010579016257930002432, coefficient := (-125032010579016257930002432) }, { argument := 414622640196363775530500096, coefficient := (-414622640196363775530500096) }, { argument := 43031795548935595274063052800, coefficient := (-43031795548935595274063052800) }, { argument := 2121656429378492700618129408, coefficient := (-2121656429378492700618129408) }, { argument := 432548178605901936416868270080, coefficient := (-432548178605901936416868270080) }, { argument := 2177124571323028457497034752, coefficient := (-2177124571323028457497034752) }, { argument := 69335177430669696098631680, coefficient := (-69335177430669696098631680) }, { argument := 2121656429378492700618129408, coefficient := (-2121656429378492700618129408) }, { argument := 1206432087293652712116191232, coefficient := (-1206432087293652712116191232) }, { argument := 2177124571323028457497034752, coefficient := (-2177124571323028457497034752) }, { argument := 33988103976514285027549249536, coefficient := (-33988103976514285027549249536) }, { argument := 1331235406668858165093728256, coefficient := (-1331235406668858165093728256) }, { argument := 43031810736224771422122147840, coefficient := (-43031810736224771422122147840) }, { argument := 2121656429378492700618129408, coefficient := (-2121656429378492700618129408) }, { argument := 69335177430669696098631680, coefficient := (-69335177430669696098631680) }, { argument := 1331235406668858165093728256, coefficient := (-1331235406668858165093728256) }, { argument := 69335177430669696098631680, coefficient := (-69335177430669696098631680) }, { argument := 2135523464864626639837855744, coefficient := (-2135523464864626639837855744) }, { argument := 1206432087293652712116191232, coefficient := (-1206432087293652712116191232) }, { argument := 414622640196363775530500096, coefficient := (-414622640196363775530500096) }, { argument := 4032014757751994794792452096, coefficient := (-4032014757751994794792452096) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 141043510029903552261855903744, coefficient := (-141043510029903552261855903744) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 141043576851386357527577886720, coefficient := (-141043576851386357527577886720) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 4031977839823375147902959616, coefficient := (-4031977839823375147902959616) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 125358464914731705078644736, coefficient := (-125358464914731705078644736) }] }

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

end TermShard8


end Parent0

namespace Parent0

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 17962011783377246024808952571625472
def positiveArguments : Array ℕ := #[
    1175, 1, 1, 1, 1, 1,
    93, 1113, 1665, 483, 93, 1929,
    969, 93, 1113, 93, 1
  ]
def positiveCoefficients : Array ℕ := #[
    186186181908521193344828283289600, 158456325028528675187087900672, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168,
    3597763239173136423925579776, 86114203982789265372670328832, 64411567669067442428345057280, 74740629871854834097034625024, 3597763239173136423925579776, 74624572993171829696262832128,
    74972743629220842898578210816, 3597763239173136423925579776, 86114203982789265372670328832, 3597763239173136423925579776, 79228162514264337593543950336
  ]
def positiveScales : Array ℕ := #[
    10, 0, 0, 0, 0, 0,
    6, 10, 10, 8, 6, 10,
    9, 6, 10, 6, 0
  ]
def negativeArguments : Array ℕ := #[
    31365273, 326914995, 31365273, 424731, 577512711, 52311,
    19959051513, 1294419, 41181, 159672470721, 21147, 21147,
    715659, 38955, 1294419, 715659, 4620043071, 41181,
    38955, 52311, 465873965, 790320091, 465873949, 3437217,
    4371, 119499135, 108159, 3441, 955993431, 1767,
    1767, 59799, 3255, 108159, 59799, 27497385,
    3441, 3255, 4371, 430076627, 729648437, 430076611,
    1, 1, 1, 1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    18514789242657030692589797376, 192976551891937206335900221440, 18514789242657030692589797376, 125358464914731705078644736, 10653229179131186980350590976, 494063426170788021547302912,
    368179515214296409703876395008, 12225441800779286575734325248, 388943548262109719090429952, 368179650375896080782974779392, 399455536052977549336117248, 399455536052977549336117248,
    6759208149528014847976931328, 367919572680374058599055360, 12225441800779286575734325248, 6759208149528014847976931328, 10653094017531515901252206592, 388943548262109719090429952,
    367919572680374058599055360, 494063426170788021547302912, 34375431211837284278872309760, 116630659639902748325810536448, 34375430031245663561461006336, 507243698598429791015141376,
    20641463896623219229065216, 17634959682997341274798817280, 510766436420697956668145664, 16249663067554449180327936, 17634966157804511146851434496, 16688843150461326185201664,
    16688843150461326185201664, 282392793309121914133807104, 15371302901740695170580480, 510766436420697956668145664, 282392793309121914133807104, 507237223791259918962524160,
    16249663067554449180327936, 15371302901740695170580480, 20641463896623219229065216, 31734053881412973346766716928, 107677103848969497028681793536, 31734052700821352629355413504,
    39614081257132168796771975168, 39614081257132168796771975168, 158456325028528675187087900672, 158456325028528675187087900672, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    24, 28, 24, 18, 29, 15,
    34, 20, 15, 37, 14, 14,
    19, 15, 20, 19, 32, 15,
    15, 15, 28, 29, 28, 21,
    12, 26, 16, 11, 29, 10,
    10, 15, 11, 16, 15, 24,
    11, 11, 12, 28, 29, 28,
    0, 0, 0, 0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10198445041452361, 0, 0, 0, 0, 0,
    6539158811107971, 10120237877341959, 10701306461953989, 8915879378478017, 6539158811107971, 10913637427705176,
    9920352855028171, 6539158811107971, 10120237877341959, 6539158811107971, 0
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    24902664788559998, 28284340311535961, 24902664788559998, 18696189885552550, 29105277459558077, 15674826729059175,
    34216324111933341, 20303873258815179, 15329691242970910, 37216324641557956, 14368165390785547, 14368165390785547,
    19448912804669952, 15249520894286927, 20303873258815179, 19448912804669952, 32105259155417304, 15329691242970910,
    15249520894286927, 15674826729059175, 28795364468508291, 29557861842984200, 28795364418960295, 21712809504908898,
    12093747662785669, 26832424935561855, 16722794192703879, 11748612176955137, 29832425465258030, 10787086325046961,
    10787086325046961, 15867833740861174, 11668441828086828, 16722794192703879, 15867833740861174, 24712791089240334,
    11748612176955137, 11668441828086828, 12093747662785669, 28680018487665498, 29442626263684090, 28680018433993386,
    0, 0, 0, 0, 1584962500724866
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 47
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
noncomputable def positiveFloor : ℝ := 11456637961 / 500000000000
noncomputable def negativeCeiling : ℝ := 279054261 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 18514789242657030692589797376, coefficient := (-18514789242657030692589797376) }, { argument := 192976551891937206335900221440, coefficient := (-192976551891937206335900221440) }, { argument := 18514789242657030692589797376, coefficient := (-18514789242657030692589797376) }, { argument := 125358464914731705078644736, coefficient := (-125358464914731705078644736) }, { argument := 10653229179131186980350590976, coefficient := (-10653229179131186980350590976) }, { argument := 494063426170788021547302912, coefficient := (-494063426170788021547302912) }, { argument := 368179515214296409703876395008, coefficient := (-368179515214296409703876395008) }, { argument := 12225441800779286575734325248, coefficient := (-12225441800779286575734325248) }, { argument := 388943548262109719090429952, coefficient := (-388943548262109719090429952) }, { argument := 368179650375896080782974779392, coefficient := (-368179650375896080782974779392) }, { argument := 399455536052977549336117248, coefficient := (-399455536052977549336117248) }, { argument := 399455536052977549336117248, coefficient := (-399455536052977549336117248) }, { argument := 6759208149528014847976931328, coefficient := (-6759208149528014847976931328) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 12225441800779286575734325248, coefficient := (-12225441800779286575734325248) }, { argument := 6759208149528014847976931328, coefficient := (-6759208149528014847976931328) }, { argument := 10653094017531515901252206592, coefficient := (-10653094017531515901252206592) }, { argument := 388943548262109719090429952, coefficient := (-388943548262109719090429952) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 494063426170788021547302912, coefficient := (-494063426170788021547302912) }, { argument := 34375431211837284278872309760, coefficient := (-34375431211837284278872309760) }, { argument := 116630659639902748325810536448, coefficient := (-116630659639902748325810536448) }, { argument := 34375430031245663561461006336, coefficient := (-34375430031245663561461006336) }, { argument := 507243698598429791015141376, coefficient := (-507243698598429791015141376) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 17634959682997341274798817280, coefficient := (-17634959682997341274798817280) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 17634966157804511146851434496, coefficient := (-17634966157804511146851434496) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 507237223791259918962524160, coefficient := (-507237223791259918962524160) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 31734053881412973346766716928, coefficient := (-31734053881412973346766716928) }, { argument := 107677103848969497028681793536, coefficient := (-107677103848969497028681793536) }, { argument := 31734052700821352629355413504, coefficient := (-31734052700821352629355413504) }, { argument := 39614081257132168796771975168, coefficient := (-39614081257132168796771975168) }, { argument := 39614081257132168796771975168, coefficient := (-39614081257132168796771975168) }, { argument := 186186181908521193344828283289600, coefficient := 186186181908521193344828283289600 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 86114203982789265372670328832, coefficient := 86114203982789265372670328832 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 74740629871854834097034625024, coefficient := 74740629871854834097034625024 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 74972743629220842898578210816, coefficient := 74972743629220842898578210816 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 86114203982789265372670328832, coefficient := 86114203982789265372670328832 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }] }

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

end TermShard9


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
