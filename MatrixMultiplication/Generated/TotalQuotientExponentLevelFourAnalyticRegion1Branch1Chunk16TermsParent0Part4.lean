import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 16, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

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
def constantNumerator : ℤ := (-1709818059586792407499985293148160)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    579994425, 14311119, 586329195, 12072972165, 586329195, 14311119,
    7491487125, 1172750293375, 293187680875, 29966378625, 13362999649, 1995,
    1653, 49688890991, 11115, 835011715, 44517, 44517,
    31863, 1653, 144996525, 22698392775, 5674600275, 579994425,
    13362913633, 3885, 3219, 49687290479, 21645, 835006339,
    86691, 86691, 62049, 3219, 3510632851, 3510632045,
    15858267, 649716135, 13378158345, 649716135, 15858267, 3818241825,
    597724343075, 149431140575, 15273186525, 26022683527, 3885, 3219,
    96762577193, 21645, 1626075445, 86691, 86691, 62049,
    3219, 3818241825, 597724343075, 149431140575, 15273186525, 806705941849,
    122115, 101181, 2999691109367, 680355
  ]
def negativeCoefficients : Array ℕ := #[
    2674752180538332251632435200, 131996774800701082306609152, 21631729206218284125640458240, 222707027736774124954598768640, 21631729206218284125640458240, 131996774800701082306609152,
    69096772863182578460393472000, 2704178065532052410275463168000, 2704179057332776748315574272000, 69097764663906916500504576000, 61625958645543392093138845696, 301475876266398150442352640,
    15612143592367047076478976, 229149563854357294810727972864, 419912827656768852401848320, 61612989620617196427028725760, 420451177435815991956209664, 420451177435815991956209664,
    300937526487351010887991296, 15612143592367047076478976, 2674713788252228843628134400, 104677860601240738462275993600, 104677898993526841870280294400, 2674752180538332251632435200,
    61625561966758831042940895232, 293542300575177146483343360, 15201297708357387942887424, 229142182795544569555258966016, 408862490086853882601799680, 61612592941832635376830775296,
    409386672766452413220519936, 409386672766452413220519936, 293018117895578615864623104, 15201297708357387942887424, 8094968217394289666951217152, 8094966358884824240713891840,
    146266696400776874988404736, 23970294525809449977061048320, 246783463167776733057798635520, 23970294525809449977061048320, 146266696400776874988404736, 70434129757308692882207539200,
    2756516995832672779506601164800, 2756518006829540169250714419200, 70435140754176082626320793600, 60004222891713302827529928704, 293542300575177146483343360, 15201297708357387942887424,
    223119312173979471263077236736, 408862490086853882601799680, 59991595156916743889475338240, 409386672766452413220519936, 409386672766452413220519936, 293018117895578615864623104,
    15201297708357387942887424, 70434129757308692882207539200, 2756516995832672779506601164800, 2756518006829540169250714419200, 70435140754176082626320793600, 1860137256503665364456594997248,
    9226748528890027604327792640, 477813763103233572366974976, 6916816774334367213242898448384, 12851542593811109877456568320
  ]
def negativeScales : Array ℕ := #[
    29, 23, 29, 33, 29, 23,
    32, 40, 38, 34, 33, 10,
    10, 35, 13, 29, 15, 15,
    14, 10, 27, 34, 32, 29,
    33, 11, 11, 35, 14, 29,
    16, 16, 15, 11, 31, 31,
    23, 29, 33, 29, 23, 31,
    39, 37, 33, 34, 11, 11,
    36, 14, 30, 16, 16, 15,
    11, 31, 39, 37, 33, 39,
    16, 16, 41, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29111463791988233, 23770633146734048, 29127135653515491, 33491061836222321, 29127135653515491, 23770633146734048,
    32802604989226212, 40093033000386617, 38093033529518090, 34802625697222808, 33637524840906545, 10962173043893966,
    10690871009350625, 35532204291534416, 13440220327914385, 29637221197483975, 15442068752306756, 15442068752306756,
    14959594499254218, 10690871009350625, 27111443083991923, 34401871095833543, 32401871624965016, 29111463791988233,
    33637515554424517, 11923698889934521, 11652396861500322, 35532157820625766, 14401746180099724, 29637211909047213,
    16403594604492093, 16403594604492093, 15921120345540660, 11652396861500322, 31709083978252760, 31709083647026914,
    23918731791459990, 29275234292504625, 33639160475227385, 29275234292504625, 23918731791459990, 31830261332630486,
    39120689343289482, 37120689872420956, 33830282040627275, 34599050693081957, 11923698889934521, 11652396861500322,
    36493730143719231, 14401746180099724, 30598747049659462, 16403594604492093, 16403594604492093, 15921120345540660,
    11652396861500322, 31830261332630486, 39120689343289482, 37120689872420956, 33830282040627275, 39553251926004692,
    16897880903343928, 16626578877333553, 41447951086726861, 19375928195943988
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
noncomputable def negativeCeiling : ℝ := 3216113293 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2674752180538332251632435200, coefficient := (-2674752180538332251632435200) }, { argument := 131996774800701082306609152, coefficient := (-131996774800701082306609152) }, { argument := 21631729206218284125640458240, coefficient := (-21631729206218284125640458240) }, { argument := 222707027736774124954598768640, coefficient := (-222707027736774124954598768640) }, { argument := 21631729206218284125640458240, coefficient := (-21631729206218284125640458240) }, { argument := 131996774800701082306609152, coefficient := (-131996774800701082306609152) }, { argument := 69096772863182578460393472000, coefficient := (-69096772863182578460393472000) }, { argument := 2704178065532052410275463168000, coefficient := (-2704178065532052410275463168000) }, { argument := 2704179057332776748315574272000, coefficient := (-2704179057332776748315574272000) }, { argument := 69097764663906916500504576000, coefficient := (-69097764663906916500504576000) }, { argument := 61625958645543392093138845696, coefficient := (-61625958645543392093138845696) }, { argument := 301475876266398150442352640, coefficient := (-301475876266398150442352640) }, { argument := 15612143592367047076478976, coefficient := (-15612143592367047076478976) }, { argument := 229149563854357294810727972864, coefficient := (-229149563854357294810727972864) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 61612989620617196427028725760, coefficient := (-61612989620617196427028725760) }, { argument := 420451177435815991956209664, coefficient := (-420451177435815991956209664) }, { argument := 420451177435815991956209664, coefficient := (-420451177435815991956209664) }, { argument := 300937526487351010887991296, coefficient := (-300937526487351010887991296) }, { argument := 15612143592367047076478976, coefficient := (-15612143592367047076478976) }, { argument := 2674713788252228843628134400, coefficient := (-2674713788252228843628134400) }, { argument := 104677860601240738462275993600, coefficient := (-104677860601240738462275993600) }, { argument := 104677898993526841870280294400, coefficient := (-104677898993526841870280294400) }, { argument := 2674752180538332251632435200, coefficient := (-2674752180538332251632435200) }, { argument := 61625561966758831042940895232, coefficient := (-61625561966758831042940895232) }, { argument := 293542300575177146483343360, coefficient := (-293542300575177146483343360) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 229142182795544569555258966016, coefficient := (-229142182795544569555258966016) }, { argument := 408862490086853882601799680, coefficient := (-408862490086853882601799680) }, { argument := 61612592941832635376830775296, coefficient := (-61612592941832635376830775296) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 293018117895578615864623104, coefficient := (-293018117895578615864623104) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 8094968217394289666951217152, coefficient := (-8094968217394289666951217152) }, { argument := 8094966358884824240713891840, coefficient := (-8094966358884824240713891840) }, { argument := 146266696400776874988404736, coefficient := (-146266696400776874988404736) }, { argument := 23970294525809449977061048320, coefficient := (-23970294525809449977061048320) }, { argument := 246783463167776733057798635520, coefficient := (-246783463167776733057798635520) }, { argument := 23970294525809449977061048320, coefficient := (-23970294525809449977061048320) }, { argument := 146266696400776874988404736, coefficient := (-146266696400776874988404736) }, { argument := 70434129757308692882207539200, coefficient := (-70434129757308692882207539200) }, { argument := 2756516995832672779506601164800, coefficient := (-2756516995832672779506601164800) }, { argument := 2756518006829540169250714419200, coefficient := (-2756518006829540169250714419200) }, { argument := 70435140754176082626320793600, coefficient := (-70435140754176082626320793600) }, { argument := 60004222891713302827529928704, coefficient := (-60004222891713302827529928704) }, { argument := 293542300575177146483343360, coefficient := (-293542300575177146483343360) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 223119312173979471263077236736, coefficient := (-223119312173979471263077236736) }, { argument := 408862490086853882601799680, coefficient := (-408862490086853882601799680) }, { argument := 59991595156916743889475338240, coefficient := (-59991595156916743889475338240) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 293018117895578615864623104, coefficient := (-293018117895578615864623104) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 70434129757308692882207539200, coefficient := (-70434129757308692882207539200) }, { argument := 2756516995832672779506601164800, coefficient := (-2756516995832672779506601164800) }, { argument := 2756518006829540169250714419200, coefficient := (-2756518006829540169250714419200) }, { argument := 70435140754176082626320793600, coefficient := (-70435140754176082626320793600) }, { argument := 1860137256503665364456594997248, coefficient := (-1860137256503665364456594997248) }, { argument := 9226748528890027604327792640, coefficient := (-9226748528890027604327792640) }, { argument := 477813763103233572366974976, coefficient := (-477813763103233572366974976) }, { argument := 6916816774334367213242898448384, coefficient := (-6916816774334367213242898448384) }, { argument := 12851542593811109877456568320, coefficient := (-12851542593811109877456568320) }] }

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
def constantNumerator : ℤ := (-309818626070054618654028089786368)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    50408510827, 2724909, 2724909, 1950351, 101181, 35882274841,
    35882266599, 26022683527, 3885, 3219, 96762577193, 21645,
    1626075445, 86691, 86691, 62049, 3219, 71701635109,
    71701618651, 1, 3518804433819, 62921511, 67744712126679, 658373859,
    29158749, 135489435068883, 29158749, 56782827, 1072735029, 56782827,
    658373859, 1072735029, 879705890361, 56782827, 56782827, 62921511,
    3051823432979, 4935, 4089, 1439481430297125, 27495, 390575227219035,
    110121, 110121, 78819, 4089, 824038136583, 824038122745,
    34462300747, 315, 261, 128141833637, 1755, 2153440513,
    7029, 7029, 5031, 261, 85085660707, 85085641181,
    1, 3510632851, 3510632045, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1859745796724972037376902692864, 12868018930469842069607153664, 12868018930469842069607153664, 9210272192231295412177207296, 477813763103233572366974976, 165477785193608523373046923264,
    165477747184092359494515818496, 60004222891713302827529928704, 293542300575177146483343360, 15201297708357387942887424, 223119312173979471263077236736, 408862490086853882601799680,
    59991595156916743889475338240, 409386672766452413220519936, 409386672766452413220519936, 293018117895578615864623104, 15201297708357387942887424, 165332714065278808752304160768,
    165332676115714563113329098752, 19807040628566084398385987584, 7923643168468448776512602112, 145087126268512545351401472, 305095060290033066012819062784, 1518106760224192242823200768,
    134470995078133578618372096, 305095084644430245920960937984, 134470995078133578618372096, 130932284681340589707362304, 4947117134716598497591689216, 130932284681340589707362304,
    1518106760224192242823200768, 4947117134716598497591689216, 7923686240050860017804378112, 130932284681340589707362304, 130932284681340589707362304, 145087126268512545351401472,
    109953527004518178187663900672, 372878057487387186073436160, 19309756548453979278802944, 405178002068305047573233664000, 519365865786003580602286080, 109937152985237052042730536960,
    520031719460088200577417216, 520031719460088200577417216, 372212203813302566098305024, 19309756548453979278802944, 14844551379417106751969820672, 14844551130133860177758126080,
    79464655258889812964638982144, 380811633178608190032445440, 19720602432463638412394496, 295474951279700628579417063424, 530416203355918550402334720, 79447932042537613289918038016,
    531096224129451779313106944, 531096224129451779313106944, 380131612405074961121673216, 19720602432463638412394496, 196194175925564238458009944064, 196194130901673640551421837312,
    19807040628566084398385987584, 8094968217394289666951217152, 8094966358884824240713891840, 19807040628566084398385987584
  ]
def negativeScales : Array ℕ := #[
    35, 21, 21, 20, 16, 35,
    35, 34, 11, 11, 36, 14,
    30, 16, 16, 15, 11, 36,
    36, 0, 41, 25, 45, 29,
    24, 46, 24, 25, 29, 25,
    29, 29, 39, 25, 25, 25,
    41, 12, 11, 50, 14, 48,
    16, 16, 16, 11, 39, 39,
    35, 8, 8, 36, 10, 31,
    12, 12, 12, 8, 36, 36,
    0, 31, 31, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35552948283618382, 21377776620336357, 21377776620336357, 20895302359051428, 16626578877333553, 35062552305067124,
    35062551973686409, 34599050693081957, 11923698889934521, 11652396861500322, 36493730143719231, 14401746180099724,
    30598747049659462, 16403594604492093, 16403594604492093, 15921120345540660, 11652396861500322, 36061286967894920,
    36061286636746576, 0, 41678222473694032, 25907049985278198, 45945173583167680, 29294331813206299,
    24797425489763281, 46945173698331696, 24797425489763281, 25758951341608834, 29998646644252779, 25758951341608834,
    29294331813206299, 29998646644252779, 39678230315918651, 25758951341608834, 25758951341608834, 25907049985278198,
    41472808634328642, 12268834369343761, 11997532370288072, 50354470601172500, 14746881666358438, 48472593775595555,
    16748730090759493, 16748730090759493, 16266255825241984, 11997532370288072, 39583920150816281, 39583920126589230,
    35004299969806341, 8299208018387279, 8027905996569885, 36898950587957878, 10777255315595305, 31003996324867978,
    12779103740003643, 12779103740003643, 12296629474285503, 8027905996569885, 36308196967153973, 36308196636075077,
    0, 31709083978252760, 31709083647026914, 0
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
noncomputable def negativeCeiling : ℝ := 1169503343 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1859745796724972037376902692864, coefficient := (-1859745796724972037376902692864) }, { argument := 12868018930469842069607153664, coefficient := (-12868018930469842069607153664) }, { argument := 12868018930469842069607153664, coefficient := (-12868018930469842069607153664) }, { argument := 9210272192231295412177207296, coefficient := (-9210272192231295412177207296) }, { argument := 477813763103233572366974976, coefficient := (-477813763103233572366974976) }, { argument := 165477785193608523373046923264, coefficient := (-165477785193608523373046923264) }, { argument := 165477747184092359494515818496, coefficient := (-165477747184092359494515818496) }, { argument := 60004222891713302827529928704, coefficient := (-60004222891713302827529928704) }, { argument := 293542300575177146483343360, coefficient := (-293542300575177146483343360) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 223119312173979471263077236736, coefficient := (-223119312173979471263077236736) }, { argument := 408862490086853882601799680, coefficient := (-408862490086853882601799680) }, { argument := 59991595156916743889475338240, coefficient := (-59991595156916743889475338240) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 293018117895578615864623104, coefficient := (-293018117895578615864623104) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 165332714065278808752304160768, coefficient := (-165332714065278808752304160768) }, { argument := 165332676115714563113329098752, coefficient := (-165332676115714563113329098752) }, { argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }, { argument := 7923643168468448776512602112, coefficient := (-7923643168468448776512602112) }, { argument := 145087126268512545351401472, coefficient := (-145087126268512545351401472) }, { argument := 305095060290033066012819062784, coefficient := (-305095060290033066012819062784) }, { argument := 1518106760224192242823200768, coefficient := (-1518106760224192242823200768) }, { argument := 134470995078133578618372096, coefficient := (-134470995078133578618372096) }, { argument := 305095084644430245920960937984, coefficient := (-305095084644430245920960937984) }, { argument := 134470995078133578618372096, coefficient := (-134470995078133578618372096) }, { argument := 130932284681340589707362304, coefficient := (-130932284681340589707362304) }, { argument := 4947117134716598497591689216, coefficient := (-4947117134716598497591689216) }, { argument := 130932284681340589707362304, coefficient := (-130932284681340589707362304) }, { argument := 1518106760224192242823200768, coefficient := (-1518106760224192242823200768) }, { argument := 4947117134716598497591689216, coefficient := (-4947117134716598497591689216) }, { argument := 7923686240050860017804378112, coefficient := (-7923686240050860017804378112) }, { argument := 130932284681340589707362304, coefficient := (-130932284681340589707362304) }, { argument := 130932284681340589707362304, coefficient := (-130932284681340589707362304) }, { argument := 145087126268512545351401472, coefficient := (-145087126268512545351401472) }, { argument := 109953527004518178187663900672, coefficient := (-109953527004518178187663900672) }, { argument := 372878057487387186073436160, coefficient := (-372878057487387186073436160) }, { argument := 19309756548453979278802944, coefficient := (-19309756548453979278802944) }, { argument := 405178002068305047573233664000, coefficient := (-405178002068305047573233664000) }, { argument := 519365865786003580602286080, coefficient := (-519365865786003580602286080) }, { argument := 109937152985237052042730536960, coefficient := (-109937152985237052042730536960) }, { argument := 520031719460088200577417216, coefficient := (-520031719460088200577417216) }, { argument := 520031719460088200577417216, coefficient := (-520031719460088200577417216) }, { argument := 372212203813302566098305024, coefficient := (-372212203813302566098305024) }, { argument := 19309756548453979278802944, coefficient := (-19309756548453979278802944) }, { argument := 14844551379417106751969820672, coefficient := (-14844551379417106751969820672) }, { argument := 14844551130133860177758126080, coefficient := (-14844551130133860177758126080) }, { argument := 79464655258889812964638982144, coefficient := (-79464655258889812964638982144) }, { argument := 380811633178608190032445440, coefficient := (-380811633178608190032445440) }, { argument := 19720602432463638412394496, coefficient := (-19720602432463638412394496) }, { argument := 295474951279700628579417063424, coefficient := (-295474951279700628579417063424) }, { argument := 530416203355918550402334720, coefficient := (-530416203355918550402334720) }, { argument := 79447932042537613289918038016, coefficient := (-79447932042537613289918038016) }, { argument := 531096224129451779313106944, coefficient := (-531096224129451779313106944) }, { argument := 531096224129451779313106944, coefficient := (-531096224129451779313106944) }, { argument := 380131612405074961121673216, coefficient := (-380131612405074961121673216) }, { argument := 19720602432463638412394496, coefficient := (-19720602432463638412394496) }, { argument := 196194175925564238458009944064, coefficient := (-196194175925564238458009944064) }, { argument := 196194130901673640551421837312, coefficient := (-196194130901673640551421837312) }, { argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }, { argument := 8094968217394289666951217152, coefficient := (-8094968217394289666951217152) }, { argument := 8094966358884824240713891840, coefficient := (-8094966358884824240713891840) }, { argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
