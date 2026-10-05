import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
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

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-171307330785227598772172843122688)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    30595339165, 4166242969, 136609010969, 9956169677543, 32614455, 84320829,
    70571733, 2002366335, 1244391897275, 70571733, 64943265, 32976951,
    32614455, 64218273, 2002366335, 64218273, 17076077253, 84320829,
    68579104293, 37589710337127, 107677, 1496585885690061, 34075, 4089,
    107677, 213991, 34075, 3302549, 211265, 150359008985335,
    107677, 4089, 211265, 4089, 107677, 107677,
    68579104293, 291399937757, 11400863484451, 11400863960611, 291400874205, 42171189,
    1091114025, 6873, 21154673703, 2175, 261, 6873,
    13659, 2175, 210801, 13485, 1091114025, 6873,
    261, 13485, 261, 6873, 6873, 42171189,
    3862969939, 604122185099, 151030568609, 15452057253
  ]
def negativeCoefficients : Array ℕ := #[
    282192195712548745695796920320, 76853617798034837168302587904, 307616145447720200345485312, 22419301024910043058655985664, 150407626122129213562552320, 194430594080753312184926208,
    2603637394978325592388141056, 4617142415444595590477905920, 22416971539482218147191193600, 2603637394978325592388141056, 149748973595762367953633280, 152079343857065067968200704,
    150407626122129213562552320, 148077255860826513547984896, 4617142415444595590477905920, 148077255860826513547984896, 307615260614242411795709952, 194430594080753312184926208,
    308852828539357182535139328, 42322251366812509693173301248, 2033961023103819150700576768, 421251477320106402594491990016, 1287317103230265285253529600, 77239026193815917115211776,
    2033961023103819150700576768, 2021087852071516497848041472, 1287317103230265285253529600, 31191693411269327861693022208, 1995341510006911192142970880, 42322298552384485366442229760,
    2033961023103819150700576768, 77239026193815917115211776, 1995341510006911192142970880, 77239026193815917115211776, 2033961023103819150700576768, 2033961023103819150700576768,
    308852828539357182535139328, 2624697302196421855956434944, 102689849080550836434624315392, 102689853369418833572095066112, 2624705736970149559648911360, 194480282691758858075897856,
    20127501174410125544679014400, 2077236789552836579438886912, 195117425881037272615458177024, 1314706828830909227492966400, 78882409729854553649577984, 2077236789552836579438886912,
    2064089721264527487163957248, 1314706828830909227492966400, 31855346462572930582154575872, 2037795584687909302614097920, 20127501174410125544679014400, 2077236789552836579438886912,
    78882409729854553649577984, 2037795584687909302614097920, 78882409729854553649577984, 2077236789552836579438886912, 2077236789552836579438886912, 194480282691758858075897856,
    17814804457291599527444217856, 696505458610715190057840410624, 696505561609263647119728705536, 17815009097399902728961916928
  ]
def negativeScales : Array ℕ := #[
    34, 31, 36, 43, 24, 26,
    26, 30, 40, 26, 25, 24,
    24, 25, 30, 25, 33, 26,
    35, 45, 16, 50, 15, 11,
    16, 17, 15, 21, 17, 47,
    16, 11, 17, 11, 16, 16,
    35, 38, 43, 43, 38, 25,
    30, 12, 34, 11, 8, 12,
    13, 11, 17, 13, 30, 12,
    8, 13, 8, 12, 12, 25,
    31, 39, 37, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34832592842385931, 31956099843165691, 36991261713795772, 43178727956237676, 24959008197075949, 26329385715108744,
    26072587102285461, 30899058799157535, 40178578044709114, 26072587102285461, 25952676592554119, 24974954695499376,
    24959008197075949, 25936480540175077, 30899058799157535, 25936480540175077, 33991257563990411, 26329385715108744,
    35997050032915572, 45095403031683320, 16716350595088157, 50410596497538173, 15056426036579935, 11997532370288072,
    16716350595088157, 17707190595782487, 15056426036579935, 21655148536280831, 17688694252134803, 47095404640159961,
    16716350595088157, 11997532370288072, 17688694252134803, 11997532370288072, 16716350595088157, 16716350595088157,
    35997050032915572, 38084209613003916, 43374208329641408, 43374208389895937, 38084214249266797, 25329754362618277,
    30023154729897250, 12746724244235141, 34300257382112476, 11086799685623454, 8027905996569885, 12746724244235141,
    13737564244911302, 11086799685623454, 17685522185351374, 13719067901235608, 30023154729897250, 12746724244235141,
    8027905996569885, 13719067901235608, 8027905996569885, 12746724244235141, 12746724244235141, 25329754362618277,
    31847063306420562, 39136049411207201, 37136049624551522, 33847079878681219
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
noncomputable def negativeCeiling : ℝ := 1359075209 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 282192195712548745695796920320, coefficient := (-282192195712548745695796920320) }, { argument := 76853617798034837168302587904, coefficient := (-76853617798034837168302587904) }, { argument := 307616145447720200345485312, coefficient := (-307616145447720200345485312) }, { argument := 22419301024910043058655985664, coefficient := (-22419301024910043058655985664) }, { argument := 150407626122129213562552320, coefficient := (-150407626122129213562552320) }, { argument := 194430594080753312184926208, coefficient := (-194430594080753312184926208) }, { argument := 2603637394978325592388141056, coefficient := (-2603637394978325592388141056) }, { argument := 4617142415444595590477905920, coefficient := (-4617142415444595590477905920) }, { argument := 22416971539482218147191193600, coefficient := (-22416971539482218147191193600) }, { argument := 2603637394978325592388141056, coefficient := (-2603637394978325592388141056) }, { argument := 149748973595762367953633280, coefficient := (-149748973595762367953633280) }, { argument := 152079343857065067968200704, coefficient := (-152079343857065067968200704) }, { argument := 150407626122129213562552320, coefficient := (-150407626122129213562552320) }, { argument := 148077255860826513547984896, coefficient := (-148077255860826513547984896) }, { argument := 4617142415444595590477905920, coefficient := (-4617142415444595590477905920) }, { argument := 148077255860826513547984896, coefficient := (-148077255860826513547984896) }, { argument := 307615260614242411795709952, coefficient := (-307615260614242411795709952) }, { argument := 194430594080753312184926208, coefficient := (-194430594080753312184926208) }, { argument := 308852828539357182535139328, coefficient := (-308852828539357182535139328) }, { argument := 42322251366812509693173301248, coefficient := (-42322251366812509693173301248) }, { argument := 2033961023103819150700576768, coefficient := (-2033961023103819150700576768) }, { argument := 421251477320106402594491990016, coefficient := (-421251477320106402594491990016) }, { argument := 1287317103230265285253529600, coefficient := (-1287317103230265285253529600) }, { argument := 77239026193815917115211776, coefficient := (-77239026193815917115211776) }, { argument := 2033961023103819150700576768, coefficient := (-2033961023103819150700576768) }, { argument := 2021087852071516497848041472, coefficient := (-2021087852071516497848041472) }, { argument := 1287317103230265285253529600, coefficient := (-1287317103230265285253529600) }, { argument := 31191693411269327861693022208, coefficient := (-31191693411269327861693022208) }, { argument := 1995341510006911192142970880, coefficient := (-1995341510006911192142970880) }, { argument := 42322298552384485366442229760, coefficient := (-42322298552384485366442229760) }, { argument := 2033961023103819150700576768, coefficient := (-2033961023103819150700576768) }, { argument := 77239026193815917115211776, coefficient := (-77239026193815917115211776) }, { argument := 1995341510006911192142970880, coefficient := (-1995341510006911192142970880) }, { argument := 77239026193815917115211776, coefficient := (-77239026193815917115211776) }, { argument := 2033961023103819150700576768, coefficient := (-2033961023103819150700576768) }, { argument := 2033961023103819150700576768, coefficient := (-2033961023103819150700576768) }, { argument := 308852828539357182535139328, coefficient := (-308852828539357182535139328) }, { argument := 2624697302196421855956434944, coefficient := (-2624697302196421855956434944) }, { argument := 102689849080550836434624315392, coefficient := (-102689849080550836434624315392) }, { argument := 102689853369418833572095066112, coefficient := (-102689853369418833572095066112) }, { argument := 2624705736970149559648911360, coefficient := (-2624705736970149559648911360) }, { argument := 194480282691758858075897856, coefficient := (-194480282691758858075897856) }, { argument := 20127501174410125544679014400, coefficient := (-20127501174410125544679014400) }, { argument := 2077236789552836579438886912, coefficient := (-2077236789552836579438886912) }, { argument := 195117425881037272615458177024, coefficient := (-195117425881037272615458177024) }, { argument := 1314706828830909227492966400, coefficient := (-1314706828830909227492966400) }, { argument := 78882409729854553649577984, coefficient := (-78882409729854553649577984) }, { argument := 2077236789552836579438886912, coefficient := (-2077236789552836579438886912) }, { argument := 2064089721264527487163957248, coefficient := (-2064089721264527487163957248) }, { argument := 1314706828830909227492966400, coefficient := (-1314706828830909227492966400) }, { argument := 31855346462572930582154575872, coefficient := (-31855346462572930582154575872) }, { argument := 2037795584687909302614097920, coefficient := (-2037795584687909302614097920) }, { argument := 20127501174410125544679014400, coefficient := (-20127501174410125544679014400) }, { argument := 2077236789552836579438886912, coefficient := (-2077236789552836579438886912) }, { argument := 78882409729854553649577984, coefficient := (-78882409729854553649577984) }, { argument := 2037795584687909302614097920, coefficient := (-2037795584687909302614097920) }, { argument := 78882409729854553649577984, coefficient := (-78882409729854553649577984) }, { argument := 2077236789552836579438886912, coefficient := (-2077236789552836579438886912) }, { argument := 2077236789552836579438886912, coefficient := (-2077236789552836579438886912) }, { argument := 194480282691758858075897856, coefficient := (-194480282691758858075897856) }, { argument := 17814804457291599527444217856, coefficient := (-17814804457291599527444217856) }, { argument := 696505458610715190057840410624, coefficient := (-696505458610715190057840410624) }, { argument := 696505561609263647119728705536, coefficient := (-696505561609263647119728705536) }, { argument := 17815009097399902728961916928, coefficient := (-17815009097399902728961916928) }] }

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

end TermShard10


end Parent1

namespace Parent1

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 26975899741618873148783487900188672
def positiveArguments : Array ℕ := #[
    3597, 5499, 4095, 4329, 351, 75231,
    136071, 4095, 75231, 2223, 2223, 4329,
    4329, 136071, 4329, 5499, 351, 1767,
    5415, 16017, 35739, 1767, 17841, 36309,
    1767, 5415, 1767, 3855, 15375, 7635,
    15375, 3, 7, 7, 7, 7,
    4371, 105891, 80229, 44697, 4371, 44697,
    89253, 4371, 105891, 4371
  ]
def positiveCoefficients : Array ℕ := #[
    284983700563808822323977589358592, 106366129312973533307348189184, 79208819701150503526748651520, 83735037969787675156848574464, 108629238447292119122398150656, 1455179173366850679077125226496,
    2631995923212515302903105191936, 79208819701150503526748651520, 1455179173366850679077125226496, 85998147104106260971898535936, 85998147104106260971898535936, 83735037969787675156848574464,
    83735037969787675156848574464, 2631995923212515302903105191936, 83735037969787675156848574464, 106366129312973533307348189184, 108629238447292119122398150656, 34178750772144796027293007872,
    837930664091291773572344709120, 619627675288560495720602271744, 691292797875315713197184385024, 34178750772144796027293007872, 690190257527827171389852352512, 702318201350201131270504710144,
    34178750772144796027293007872, 837930664091291773572344709120, 34178750772144796027293007872, 298266178215321309983507742720, 297395751625198776977719296000, 295364756248246199964212920320,
    297395751625198776977719296000, 475368975085586025561263702016, 554597137599850363154807652352, 554597137599850363154807652352, 554597137599850363154807652352, 554597137599850363154807652352,
    84547436120568705962251124736, 2048229823437003167020986925056, 1551854553309793344920028708864, 1729131435498082567098942357504, 84547436120568705962251124736, 1729131435498082567098942357504,
    1726404098849031963680805224448, 84547436120568705962251124736, 2048229823437003167020986925056, 84547436120568705962251124736
  ]
def positiveScales : Array ℕ := #[
    11, 12, 11, 12, 8, 16,
    17, 11, 16, 11, 11, 12,
    12, 17, 12, 12, 8, 10,
    12, 13, 15, 10, 14, 15,
    10, 12, 10, 11, 13, 12,
    13, 1, 2, 2, 2, 2,
    12, 16, 16, 15, 12, 15,
    16, 12, 16, 12
  ]
def negativeArguments : Array ℕ := #[
    4156304749, 15259932201, 2077875765, 635568169, 24849017417, 24849021137,
    635575485, 8333592369, 30595339165, 4166242969, 25165827, 25165821,
    117, 57, 15, 3, 7, 141
  ]
def negativeCoefficients : Array ℕ := #[
    76670289997146615428241424384, 281496063894006304226269986816, 76660084907836901903805972480, 732760209683698797399506944, 28648966548409386244077780992, 28648970837277383381548531712,
    732768644457426501091983360, 76863822822780946434754609152, 282192195712548745695796920320, 76853617798034837168302587904, 118842257938495954999251566592, 118842229604297057781380284416,
    9269695014168927498444642189312, 4516005263313067242832005169152, 1188422437713965063903159255040, 475368975085586025561263702016, 2218388550399401452619230609408, 11171170914511271600689696997376
  ]
def negativeScales : Array ℕ := #[
    31, 33, 30, 29, 34, 34,
    29, 32, 34, 31, 24, 24,
    6, 5, 3, 1, 2, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11812578444083777, 12424953571261040, 11999647735076951, 12079818085212354, 8455327220304556, 16199039646911351,
    17054000101056622, 11999647735076951, 16199039646911351, 11118292233026989, 11118292233026989, 12079818085212354,
    12079818085212354, 17054000101056622, 12079818085212354, 12424953571261040, 8455327220304556, 10787086324520917,
    12402745622495688, 13967316333526543, 15125211646966780, 10787086324520917, 14122908861097359, 15148039576421041,
    10787086324520917, 12402745622495688, 10787086324520917, 11912515144465203, 13908298789688351, 12898412441421818,
    13908298789688351, 1584962500720924, 2807354922011143, 2807354922011143, 2807354922011143, 2807354922011143,
    12093747662785668, 16692220449909325, 16291836194705375, 15447890382538197, 12093747662785668, 15447890382538197,
    16445613041827131, 12093747662785668, 16692220449909325, 12093747662785668
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31952654304440447, 33829029502403727, 30952462263763999, 29243471631463450, 34532469754559433, 34532469970536791,
    29243488238173299, 32956291399067364, 34832592842385931, 31956099843165691, 24584962672707506, 24584962328742205,
    6870364722125690, 5832890015409720, 3906890600547867, 1584962500724866, 2807354922807594, 7139551352398794
  ]

abbrev PositiveTerm := Fin 46
abbrev NegativeTerm := Fin 18
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
noncomputable def positiveFloor : ℝ := 22747570687 / 500000000000
noncomputable def negativeCeiling : ℝ := 328668807 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 76670289997146615428241424384, coefficient := (-76670289997146615428241424384) }, { argument := 281496063894006304226269986816, coefficient := (-281496063894006304226269986816) }, { argument := 76660084907836901903805972480, coefficient := (-76660084907836901903805972480) }, { argument := 732760209683698797399506944, coefficient := (-732760209683698797399506944) }, { argument := 28648966548409386244077780992, coefficient := (-28648966548409386244077780992) }, { argument := 28648970837277383381548531712, coefficient := (-28648970837277383381548531712) }, { argument := 732768644457426501091983360, coefficient := (-732768644457426501091983360) }, { argument := 76863822822780946434754609152, coefficient := (-76863822822780946434754609152) }, { argument := 282192195712548745695796920320, coefficient := (-282192195712548745695796920320) }, { argument := 76853617798034837168302587904, coefficient := (-76853617798034837168302587904) }, { argument := 118842257938495954999251566592, coefficient := (-118842257938495954999251566592) }, { argument := 118842229604297057781380284416, coefficient := (-118842229604297057781380284416) }, { argument := 284983700563808822323977589358592, coefficient := 284983700563808822323977589358592 }, { argument := 106366129312973533307348189184, coefficient := 106366129312973533307348189184 }, { argument := 79208819701150503526748651520, coefficient := 79208819701150503526748651520 }, { argument := 83735037969787675156848574464, coefficient := 83735037969787675156848574464 }, { argument := 108629238447292119122398150656, coefficient := 108629238447292119122398150656 }, { argument := 1455179173366850679077125226496, coefficient := 1455179173366850679077125226496 }, { argument := 2631995923212515302903105191936, coefficient := 2631995923212515302903105191936 }, { argument := 79208819701150503526748651520, coefficient := 79208819701150503526748651520 }, { argument := 1455179173366850679077125226496, coefficient := 1455179173366850679077125226496 }, { argument := 85998147104106260971898535936, coefficient := 85998147104106260971898535936 }, { argument := 85998147104106260971898535936, coefficient := 85998147104106260971898535936 }, { argument := 83735037969787675156848574464, coefficient := 83735037969787675156848574464 }, { argument := 83735037969787675156848574464, coefficient := 83735037969787675156848574464 }, { argument := 2631995923212515302903105191936, coefficient := 2631995923212515302903105191936 }, { argument := 83735037969787675156848574464, coefficient := 83735037969787675156848574464 }, { argument := 106366129312973533307348189184, coefficient := 106366129312973533307348189184 }, { argument := 108629238447292119122398150656, coefficient := 108629238447292119122398150656 }, { argument := 9269695014168927498444642189312, coefficient := (-9269695014168927498444642189312) }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 837930664091291773572344709120, coefficient := 837930664091291773572344709120 }, { argument := 619627675288560495720602271744, coefficient := 619627675288560495720602271744 }, { argument := 691292797875315713197184385024, coefficient := 691292797875315713197184385024 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 690190257527827171389852352512, coefficient := 690190257527827171389852352512 }, { argument := 702318201350201131270504710144, coefficient := 702318201350201131270504710144 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 837930664091291773572344709120, coefficient := 837930664091291773572344709120 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 4516005263313067242832005169152, coefficient := (-4516005263313067242832005169152) }, { argument := 298266178215321309983507742720, coefficient := 298266178215321309983507742720 }, { argument := 297395751625198776977719296000, coefficient := 297395751625198776977719296000 }, { argument := 295364756248246199964212920320, coefficient := 295364756248246199964212920320 }, { argument := 297395751625198776977719296000, coefficient := 297395751625198776977719296000 }, { argument := 1188422437713965063903159255040, coefficient := (-1188422437713965063903159255040) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 554597137599850363154807652352, coefficient := 554597137599850363154807652352 }, { argument := 554597137599850363154807652352, coefficient := 554597137599850363154807652352 }, { argument := 554597137599850363154807652352, coefficient := 554597137599850363154807652352 }, { argument := 554597137599850363154807652352, coefficient := 554597137599850363154807652352 }, { argument := 2218388550399401452619230609408, coefficient := (-2218388550399401452619230609408) }, { argument := 84547436120568705962251124736, coefficient := 84547436120568705962251124736 }, { argument := 2048229823437003167020986925056, coefficient := 2048229823437003167020986925056 }, { argument := 1551854553309793344920028708864, coefficient := 1551854553309793344920028708864 }, { argument := 1729131435498082567098942357504, coefficient := 1729131435498082567098942357504 }, { argument := 84547436120568705962251124736, coefficient := 84547436120568705962251124736 }, { argument := 1729131435498082567098942357504, coefficient := 1729131435498082567098942357504 }, { argument := 1726404098849031963680805224448, coefficient := 1726404098849031963680805224448 }, { argument := 84547436120568705962251124736, coefficient := 84547436120568705962251124736 }, { argument := 2048229823437003167020986925056, coefficient := 2048229823437003167020986925056 }, { argument := 84547436120568705962251124736, coefficient := 84547436120568705962251124736 }, { argument := 11171170914511271600689696997376, coefficient := (-11171170914511271600689696997376) }] }

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

end TermShard11


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
