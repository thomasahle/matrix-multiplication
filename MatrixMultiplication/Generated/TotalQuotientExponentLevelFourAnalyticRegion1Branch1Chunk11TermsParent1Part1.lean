import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 11, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

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
def constantNumerator : ℤ := (-2476747528480768068715698775392256)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    51625, 54575, 4425, 948425, 1715425, 51625,
    948425, 28025, 28025, 54575, 54575, 1715425,
    54575, 69325, 4425, 2514792135599, 3718065643720875, 80185,
    150859952812886587, 25375, 3045, 80185, 159355, 25375,
    2459345, 157325, 14872292480403289, 80185, 3045, 157325,
    3045, 80185, 80185, 2514792135599, 8319, 6195,
    6549, 531, 113811, 205851, 6195, 113811,
    3363, 3363, 6549, 6549, 205851, 6549,
    8319, 531, 16312095, 422935035, 84767, 8202812661,
    26825, 3219, 84767, 168461, 26825, 2599879,
    166315, 422935035, 84767, 3219
  ]
def negativeCoefficients : Array ℕ := #[
    975168678712581736628224000, 1030892603210443550149836800, 1337374187948683524518707200, 17915241726062573047198515200, 32403462095506644562817843200, 975168678712581736628224000,
    17915241726062573047198515200, 1058754565459374456910643200, 1058754565459374456910643200, 1030892603210443550149836800, 1030892603210443550149836800, 32403462095506644562817843200,
    1030892603210443550149836800, 1309512225699752617757900800, 1337374187948683524518707200, 22651233849595820497287774208, 4186169761900093997712408576000, 1514651825715610005840855040,
    42463301704577915192741642371072, 958640396022537978380288000, 57518423761352278702817280, 1514651825715610005840855040, 1505065421755384626057052160, 958640396022537978380288000,
    23227856795626095216154378240, 1485892613834933866489446400, 4186178179555580126549543747584, 1514651825715610005840855040, 57518423761352278702817280, 1485892613834933866489446400,
    57518423761352278702817280, 1514651825715610005840855040, 1514651825715610005840855040, 22651233849595820497287774208, 78570733541985157065474048, 58510120722754904197693440,
    61853556192626613008990208, 80242451276921011471122432, 1074914503563754382831910912, 1944207725730398673769070592, 58510120722754904197693440, 1074914503563754382831910912,
    63525273927562467414638592, 63525273927562467414638592, 61853556192626613008990208, 61853556192626613008990208, 1944207725730398673769070592, 61853556192626613008990208,
    78570733541985157065474048, 80242451276921011471122432, 150452520885518604183797760, 15603548700900783585094533120, 1601203358613644863317475328, 151315185842051427232357810176,
    1013419847223825862859161600, 60805190833429551771549696, 1601203358613644863317475328, 1591069160141406604688883712, 1013419847223825862859161600, 24555162898233300657077485568,
    1570800763196930087431700480, 15603548700900783585094533120, 1601203358613644863317475328, 60805190833429551771549696
  ]
def negativeScales : Array ℕ := #[
    15, 15, 12, 19, 20, 15,
    19, 14, 14, 15, 15, 20,
    15, 16, 12, 41, 51, 16,
    57, 14, 11, 16, 17, 14,
    21, 17, 53, 16, 11, 17,
    11, 16, 16, 41, 13, 12,
    12, 9, 16, 17, 12, 16,
    11, 11, 12, 12, 17, 12,
    13, 9, 23, 28, 16, 32,
    14, 11, 16, 17, 14, 21,
    17, 28, 16, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15655782256106199, 15735952604930435, 12111461739857723, 19855174168375817, 20710134620701494, 15655782256106199,
    19855174168375817, 14774426752960191, 14774426752960191, 15735952604930435, 15735952604930435, 20710134620701494,
    15735952604930435, 16081088090814204, 12111461739857723, 41193576295206425, 51723473665191709, 16291044760249642,
    57065987492865293, 14631120201860344, 11572226512796267, 16291044760249642, 17281884760964166, 14631120201860344,
    21229842701523886, 17263388417346777, 53723476566196289, 16291044760249642, 11572226512796267, 17263388417346777,
    11572226512796267, 16291044760249642, 16291044760249642, 41193576295206425, 13022194401760635, 12596888567033151,
    12677058915753742, 9052568050804154, 16796280478009686, 17651240931578205, 12596888567033151, 16796280478009686,
    11715533063630459, 11715533063630459, 12677058915753742, 12677058915753742, 17651240931578205, 12677058915753742,
    13022194401760635, 9052568050804154, 23959438759028386, 28655860834097066, 16371215108933627, 32933471541862067,
    14711290550625444, 11652396861500322, 16371215108933627, 17362055109648151, 14711290550625444, 21310013050207869,
    17343558766030761, 28655860834097066, 16371215108933627, 11652396861500322
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
noncomputable def negativeCeiling : ℝ := 34620238227 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 975168678712581736628224000, coefficient := (-975168678712581736628224000) }, { argument := 1030892603210443550149836800, coefficient := (-1030892603210443550149836800) }, { argument := 1337374187948683524518707200, coefficient := (-1337374187948683524518707200) }, { argument := 17915241726062573047198515200, coefficient := (-17915241726062573047198515200) }, { argument := 32403462095506644562817843200, coefficient := (-32403462095506644562817843200) }, { argument := 975168678712581736628224000, coefficient := (-975168678712581736628224000) }, { argument := 17915241726062573047198515200, coefficient := (-17915241726062573047198515200) }, { argument := 1058754565459374456910643200, coefficient := (-1058754565459374456910643200) }, { argument := 1058754565459374456910643200, coefficient := (-1058754565459374456910643200) }, { argument := 1030892603210443550149836800, coefficient := (-1030892603210443550149836800) }, { argument := 1030892603210443550149836800, coefficient := (-1030892603210443550149836800) }, { argument := 32403462095506644562817843200, coefficient := (-32403462095506644562817843200) }, { argument := 1030892603210443550149836800, coefficient := (-1030892603210443550149836800) }, { argument := 1309512225699752617757900800, coefficient := (-1309512225699752617757900800) }, { argument := 1337374187948683524518707200, coefficient := (-1337374187948683524518707200) }, { argument := 22651233849595820497287774208, coefficient := (-22651233849595820497287774208) }, { argument := 4186169761900093997712408576000, coefficient := (-4186169761900093997712408576000) }, { argument := 1514651825715610005840855040, coefficient := (-1514651825715610005840855040) }, { argument := 42463301704577915192741642371072, coefficient := (-42463301704577915192741642371072) }, { argument := 958640396022537978380288000, coefficient := (-958640396022537978380288000) }, { argument := 57518423761352278702817280, coefficient := (-57518423761352278702817280) }, { argument := 1514651825715610005840855040, coefficient := (-1514651825715610005840855040) }, { argument := 1505065421755384626057052160, coefficient := (-1505065421755384626057052160) }, { argument := 958640396022537978380288000, coefficient := (-958640396022537978380288000) }, { argument := 23227856795626095216154378240, coefficient := (-23227856795626095216154378240) }, { argument := 1485892613834933866489446400, coefficient := (-1485892613834933866489446400) }, { argument := 4186178179555580126549543747584, coefficient := (-4186178179555580126549543747584) }, { argument := 1514651825715610005840855040, coefficient := (-1514651825715610005840855040) }, { argument := 57518423761352278702817280, coefficient := (-57518423761352278702817280) }, { argument := 1485892613834933866489446400, coefficient := (-1485892613834933866489446400) }, { argument := 57518423761352278702817280, coefficient := (-57518423761352278702817280) }, { argument := 1514651825715610005840855040, coefficient := (-1514651825715610005840855040) }, { argument := 1514651825715610005840855040, coefficient := (-1514651825715610005840855040) }, { argument := 22651233849595820497287774208, coefficient := (-22651233849595820497287774208) }, { argument := 78570733541985157065474048, coefficient := (-78570733541985157065474048) }, { argument := 58510120722754904197693440, coefficient := (-58510120722754904197693440) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 80242451276921011471122432, coefficient := (-80242451276921011471122432) }, { argument := 1074914503563754382831910912, coefficient := (-1074914503563754382831910912) }, { argument := 1944207725730398673769070592, coefficient := (-1944207725730398673769070592) }, { argument := 58510120722754904197693440, coefficient := (-58510120722754904197693440) }, { argument := 1074914503563754382831910912, coefficient := (-1074914503563754382831910912) }, { argument := 63525273927562467414638592, coefficient := (-63525273927562467414638592) }, { argument := 63525273927562467414638592, coefficient := (-63525273927562467414638592) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 1944207725730398673769070592, coefficient := (-1944207725730398673769070592) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 78570733541985157065474048, coefficient := (-78570733541985157065474048) }, { argument := 80242451276921011471122432, coefficient := (-80242451276921011471122432) }, { argument := 150452520885518604183797760, coefficient := (-150452520885518604183797760) }, { argument := 15603548700900783585094533120, coefficient := (-15603548700900783585094533120) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 151315185842051427232357810176, coefficient := (-151315185842051427232357810176) }, { argument := 1013419847223825862859161600, coefficient := (-1013419847223825862859161600) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 1591069160141406604688883712, coefficient := (-1591069160141406604688883712) }, { argument := 1013419847223825862859161600, coefficient := (-1013419847223825862859161600) }, { argument := 24555162898233300657077485568, coefficient := (-24555162898233300657077485568) }, { argument := 1570800763196930087431700480, coefficient := (-1570800763196930087431700480) }, { argument := 15603548700900783585094533120, coefficient := (-15603548700900783585094533120) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }] }

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
def constantNumerator : ℤ := (-56164880988793759070646595223552)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    166315, 3219, 84767, 84767, 16312095, 2322278432731,
    90857782183973, 90857785993253, 2322285924315, 219067, 163135, 172457,
    13983, 2997023, 5420743, 163135, 2997023, 88559,
    88559, 172457, 172457, 5420743, 172457, 219067,
    13983, 435361, 324205, 342731, 27789, 5956109,
    10772869, 324205, 5956109, 175997, 175997, 342731,
    342731, 10772869, 342731, 435361, 27789, 42171189,
    1091114025, 6873, 21154673703, 2175, 261, 6873,
    13659, 2175, 210801, 13485, 1091114025, 6873,
    261, 13485, 261, 6873, 6873, 42171189,
    69325, 51625, 54575, 4425
  ]
def negativeCoefficients : Array ℕ := #[
    1570800763196930087431700480, 60805190833429551771549696, 1601203358613644863317475328, 1601203358613644863317475328, 150452520885518604183797760, 2614653071074467765387526144,
    102296768496862623261526065152, 102296772785730620398996815872, 2614661505848195469080002560, 2069029316605609136057483264, 1540766512365879143872593920, 1628810313072500809236742144,
    2113051216958919968739557376, 28306081927178865414573654016, 51197470110900498409252192256, 1540766512365879143872593920, 28306081927178865414573654016, 1672832213425811641918816256,
    1672832213425811641918816256, 1628810313072500809236742144, 1628810313072500809236742144, 51197470110900498409252192256, 1628810313072500809236742144, 2069029316605609136057483264,
    2113051216958919968739557376, 2055934194348611609879904256, 1531014825578753326506311680, 1618501387040396373735243776, 2099677475079433133494370304, 28126929509918239684101668864,
    50873435489945431963624013824, 1531014825578753326506311680, 28126929509918239684101668864, 1662244667771217897349709824, 1662244667771217897349709824, 1618501387040396373735243776,
    1618501387040396373735243776, 50873435489945431963624013824, 1618501387040396373735243776, 2055934194348611609879904256, 2099677475079433133494370304, 194480282691758858075897856,
    20127501174410125544679014400, 2077236789552836579438886912, 195117425881037272615458177024, 1314706828830909227492966400, 78882409729854553649577984, 2077236789552836579438886912,
    2064089721264527487163957248, 1314706828830909227492966400, 31855346462572930582154575872, 2037795584687909302614097920, 20127501174410125544679014400, 2077236789552836579438886912,
    78882409729854553649577984, 2037795584687909302614097920, 78882409729854553649577984, 2077236789552836579438886912, 2077236789552836579438886912, 194480282691758858075897856,
    1309512225699752617757900800, 975168678712581736628224000, 1030892603210443550149836800, 1337374187948683524518707200
  ]
def negativeScales : Array ℕ := #[
    17, 11, 16, 16, 23, 41,
    46, 46, 41, 17, 17, 17,
    13, 21, 22, 17, 21, 16,
    16, 17, 17, 22, 17, 17,
    13, 18, 18, 18, 14, 22,
    23, 18, 22, 17, 17, 18,
    18, 23, 18, 18, 14, 25,
    30, 12, 34, 11, 8, 12,
    13, 11, 17, 13, 30, 12,
    8, 13, 8, 12, 12, 25,
    16, 15, 15, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    17343558766030761, 11652396861500322, 16371215108933627, 16371215108933627, 23959438759028386, 41078678095106125,
    46368675323530472, 46368675384016532, 41078682749179254, 17741012649401125, 17315706814483911, 17395877163167900,
    13771386298616460, 21515098724867337, 22370059179012165, 17315706814483911, 21515098724867337, 16434351310982556,
    16434351310982556, 17395877163167900, 17395877163167900, 22370059179012165, 17395877163167900, 17741012649401125,
    13771386298616460, 18731852650081573, 18306546815198435, 18386717163882422, 14762226299267708, 22505938725581746,
    23360899179726688, 18306546815198435, 22505938725581746, 17425191311697072, 17425191311697072, 18386717163882422,
    18386717163882422, 23360899179726688, 18386717163882422, 18731852650081573, 14762226299267708, 25329754362618277,
    30023154729897250, 12746724244235141, 34300257382112476, 11086799685623454, 8027905996569885, 12746724244235141,
    13737564244911302, 11086799685623454, 17685522185351374, 13719067901235608, 30023154729897250, 12746724244235141,
    8027905996569885, 13719067901235608, 8027905996569885, 12746724244235141, 12746724244235141, 25329754362618277,
    16081088090814204, 15655782256106199, 15735952604930435, 12111461739857723
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
noncomputable def negativeCeiling : ℝ := 318419361 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1570800763196930087431700480, coefficient := (-1570800763196930087431700480) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 1601203358613644863317475328, coefficient := (-1601203358613644863317475328) }, { argument := 150452520885518604183797760, coefficient := (-150452520885518604183797760) }, { argument := 2614653071074467765387526144, coefficient := (-2614653071074467765387526144) }, { argument := 102296768496862623261526065152, coefficient := (-102296768496862623261526065152) }, { argument := 102296772785730620398996815872, coefficient := (-102296772785730620398996815872) }, { argument := 2614661505848195469080002560, coefficient := (-2614661505848195469080002560) }, { argument := 2069029316605609136057483264, coefficient := (-2069029316605609136057483264) }, { argument := 1540766512365879143872593920, coefficient := (-1540766512365879143872593920) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 2113051216958919968739557376, coefficient := (-2113051216958919968739557376) }, { argument := 28306081927178865414573654016, coefficient := (-28306081927178865414573654016) }, { argument := 51197470110900498409252192256, coefficient := (-51197470110900498409252192256) }, { argument := 1540766512365879143872593920, coefficient := (-1540766512365879143872593920) }, { argument := 28306081927178865414573654016, coefficient := (-28306081927178865414573654016) }, { argument := 1672832213425811641918816256, coefficient := (-1672832213425811641918816256) }, { argument := 1672832213425811641918816256, coefficient := (-1672832213425811641918816256) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 51197470110900498409252192256, coefficient := (-51197470110900498409252192256) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 2069029316605609136057483264, coefficient := (-2069029316605609136057483264) }, { argument := 2113051216958919968739557376, coefficient := (-2113051216958919968739557376) }, { argument := 2055934194348611609879904256, coefficient := (-2055934194348611609879904256) }, { argument := 1531014825578753326506311680, coefficient := (-1531014825578753326506311680) }, { argument := 1618501387040396373735243776, coefficient := (-1618501387040396373735243776) }, { argument := 2099677475079433133494370304, coefficient := (-2099677475079433133494370304) }, { argument := 28126929509918239684101668864, coefficient := (-28126929509918239684101668864) }, { argument := 50873435489945431963624013824, coefficient := (-50873435489945431963624013824) }, { argument := 1531014825578753326506311680, coefficient := (-1531014825578753326506311680) }, { argument := 28126929509918239684101668864, coefficient := (-28126929509918239684101668864) }, { argument := 1662244667771217897349709824, coefficient := (-1662244667771217897349709824) }, { argument := 1662244667771217897349709824, coefficient := (-1662244667771217897349709824) }, { argument := 1618501387040396373735243776, coefficient := (-1618501387040396373735243776) }, { argument := 1618501387040396373735243776, coefficient := (-1618501387040396373735243776) }, { argument := 50873435489945431963624013824, coefficient := (-50873435489945431963624013824) }, { argument := 1618501387040396373735243776, coefficient := (-1618501387040396373735243776) }, { argument := 2055934194348611609879904256, coefficient := (-2055934194348611609879904256) }, { argument := 2099677475079433133494370304, coefficient := (-2099677475079433133494370304) }, { argument := 194480282691758858075897856, coefficient := (-194480282691758858075897856) }, { argument := 20127501174410125544679014400, coefficient := (-20127501174410125544679014400) }, { argument := 2077236789552836579438886912, coefficient := (-2077236789552836579438886912) }, { argument := 195117425881037272615458177024, coefficient := (-195117425881037272615458177024) }, { argument := 1314706828830909227492966400, coefficient := (-1314706828830909227492966400) }, { argument := 78882409729854553649577984, coefficient := (-78882409729854553649577984) }, { argument := 2077236789552836579438886912, coefficient := (-2077236789552836579438886912) }, { argument := 2064089721264527487163957248, coefficient := (-2064089721264527487163957248) }, { argument := 1314706828830909227492966400, coefficient := (-1314706828830909227492966400) }, { argument := 31855346462572930582154575872, coefficient := (-31855346462572930582154575872) }, { argument := 2037795584687909302614097920, coefficient := (-2037795584687909302614097920) }, { argument := 20127501174410125544679014400, coefficient := (-20127501174410125544679014400) }, { argument := 2077236789552836579438886912, coefficient := (-2077236789552836579438886912) }, { argument := 78882409729854553649577984, coefficient := (-78882409729854553649577984) }, { argument := 2037795584687909302614097920, coefficient := (-2037795584687909302614097920) }, { argument := 78882409729854553649577984, coefficient := (-78882409729854553649577984) }, { argument := 2077236789552836579438886912, coefficient := (-2077236789552836579438886912) }, { argument := 2077236789552836579438886912, coefficient := (-2077236789552836579438886912) }, { argument := 194480282691758858075897856, coefficient := (-194480282691758858075897856) }, { argument := 1309512225699752617757900800, coefficient := (-1309512225699752617757900800) }, { argument := 975168678712581736628224000, coefficient := (-975168678712581736628224000) }, { argument := 1030892603210443550149836800, coefficient := (-1030892603210443550149836800) }, { argument := 1337374187948683524518707200, coefficient := (-1337374187948683524518707200) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
