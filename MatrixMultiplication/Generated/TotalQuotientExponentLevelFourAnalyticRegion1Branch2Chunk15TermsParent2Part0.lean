import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 15, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

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
def constantNumerator : ℤ := (-33511499364253047469708061813243904)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    22058149, 1479195483, 985, 1127, 16563, 28641,
    739597711, 16563, 985, 963, 237, 963,
    28641, 237, 11029105, 1127, 30504356345879, 2097798309314093,
    5615, 21616775113345935, 6305, 855, 5615, 2725,
    6305, 17675, 5415, 2097798499630637, 5615, 855,
    5415, 855, 11235, 2725, 30750635390999, 18676937174775657,
    420198465, 344796696481882619, 6649146825, 198954675, 344782989614251493, 198966195,
    198966195, 17022083985, 198931635, 6649146825, 17022083985, 18704354357266647,
    198954675, 198931635, 420198465, 2403, 37647, 29637,
    931563, 29637, 29637, 15219, 15219, 515043,
    28035, 931563, 515043, 2403
  ]
def negativeCoefficients : Array ℕ := #[
    104166663511744581700843208704, 6985303170531376077911692935168, 19052670917126555793369333760, 21799350379290993278301765632, 320375013604433648330534289408, 553997510393321507084153389056,
    6985302882467020622863334899712, 320375013604433648330534289408, 19052670917126555793369333760, 18627129028622206323872759808, 18336986831914695321943277568, 18627129028622206323872759808,
    553997510393321507084153389056, 18336986831914695321943277568, 104166951576100036749201244160, 21799350379290993278301765632, 137379407872477489395855785984, 18895287368250811486101890400256,
    217219791268356570111205703680, 194706600690833128600720921067520, 121956436682723791144359034880, 8269052606164063554990243840, 217219791268356570111205703680, 210836662940791328068757094400,
    121956436682723791144359034880, 2735073774296137044855252582400, 209482666022822943393086177280, 18895289082469844767783102971904, 217219791268356570111205703680, 8269052606164063554990243840,
    209482666022822943393086177280, 8269052606164063554990243840, 217316505333925740445182197760, 210836662940791328068757094400, 138488550088309082967196565504, 5257090456296363324336601300992,
    7751293544020600444881469440, 194103284224298071505741836976128, 61327554894646715549850009600, 7340131943986119772314009600, 194095567943803577034889354018816, 7340556956969578040383242240,
    7340556956969578040383242240, 314002026872485018104244469760, 7339281918019203236175544320, 61327554894646715549850009600, 314002026872485018104244469760, 5264807707099486540043158290432,
    7340131943986119772314009600, 7339281918019203236175544320, 7751293544020600444881469440, 363131093066744238352367616, 355565861961187066720026624, 279913550905615350396616704,
    8798363775762990608412573696, 279913550905615350396616704, 279913550905615350396616704, 287478782011172522028957696, 287478782011172522028957696, 4864443600873261359595257856,
    264783088694501007131934720, 8798363775762990608412573696, 4864443600873261359595257856, 363131093066744238352367616
  ]
def negativeScales : Array ℕ := #[
    24, 30, 9, 10, 14, 14,
    29, 14, 9, 9, 7, 9,
    14, 7, 23, 10, 44, 50,
    12, 54, 12, 9, 12, 11,
    12, 14, 12, 50, 12, 9,
    12, 9, 13, 11, 44, 54,
    28, 58, 32, 27, 58, 27,
    27, 33, 27, 32, 33, 54,
    27, 27, 28, 11, 15, 14,
    19, 14, 14, 13, 13, 18,
    14, 19, 18, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    24394808397091813, 30462165578308733, 9943979923756826, 10138271800172222, 14015676386513096, 14805794245429119,
    29462165518813960, 14015676386513096, 9943979923756826, 9911391993193157, 7888743252462684, 9911391993193157,
    14805794245429119, 7888743252462684, 23394812386740982, 10138271800172222, 44794080523662267, 50897797405643248,
    12455070307288020, 54263000829660352, 12622280655225937, 9739780609952834, 12455070307288020, 11412040514551662,
    12622280655225937, 14109422594584124, 12402745622495697, 50897797536527490, 12455070307288020, 9739780609952834,
    12402745622495697, 9739780609952834, 13455712504067328, 11412040514551662, 44805681454988173, 54052107405522944,
    28646495650922458, 58258523565029466, 32630522089303671, 27567864558711220, 58258466211744969, 27567948092137737,
    27567948092137737, 33986688642546430, 27567697477346790, 32630522089303671, 33986688642546430, 54054223685548942,
    27567864558711220, 27567697477346790, 28646495650922458, 11230620933129867, 15200247284086348, 14855111799946705,
    19829293815042335, 14855111799946705, 14855111799946705, 13893585949743706, 13893585949743706, 18974333375367452,
    14774941449737867, 19829293815042335, 18974333375367452, 11230620933129867
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
noncomputable def negativeCeiling : ℝ := 43606389547 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 104166663511744581700843208704, coefficient := (-104166663511744581700843208704) }, { argument := 6985303170531376077911692935168, coefficient := (-6985303170531376077911692935168) }, { argument := 19052670917126555793369333760, coefficient := (-19052670917126555793369333760) }, { argument := 21799350379290993278301765632, coefficient := (-21799350379290993278301765632) }, { argument := 320375013604433648330534289408, coefficient := (-320375013604433648330534289408) }, { argument := 553997510393321507084153389056, coefficient := (-553997510393321507084153389056) }, { argument := 6985302882467020622863334899712, coefficient := (-6985302882467020622863334899712) }, { argument := 320375013604433648330534289408, coefficient := (-320375013604433648330534289408) }, { argument := 19052670917126555793369333760, coefficient := (-19052670917126555793369333760) }, { argument := 18627129028622206323872759808, coefficient := (-18627129028622206323872759808) }, { argument := 18336986831914695321943277568, coefficient := (-18336986831914695321943277568) }, { argument := 18627129028622206323872759808, coefficient := (-18627129028622206323872759808) }, { argument := 553997510393321507084153389056, coefficient := (-553997510393321507084153389056) }, { argument := 18336986831914695321943277568, coefficient := (-18336986831914695321943277568) }, { argument := 104166951576100036749201244160, coefficient := (-104166951576100036749201244160) }, { argument := 21799350379290993278301765632, coefficient := (-21799350379290993278301765632) }, { argument := 137379407872477489395855785984, coefficient := (-137379407872477489395855785984) }, { argument := 18895287368250811486101890400256, coefficient := (-18895287368250811486101890400256) }, { argument := 217219791268356570111205703680, coefficient := (-217219791268356570111205703680) }, { argument := 194706600690833128600720921067520, coefficient := (-194706600690833128600720921067520) }, { argument := 121956436682723791144359034880, coefficient := (-121956436682723791144359034880) }, { argument := 8269052606164063554990243840, coefficient := (-8269052606164063554990243840) }, { argument := 217219791268356570111205703680, coefficient := (-217219791268356570111205703680) }, { argument := 210836662940791328068757094400, coefficient := (-210836662940791328068757094400) }, { argument := 121956436682723791144359034880, coefficient := (-121956436682723791144359034880) }, { argument := 2735073774296137044855252582400, coefficient := (-2735073774296137044855252582400) }, { argument := 209482666022822943393086177280, coefficient := (-209482666022822943393086177280) }, { argument := 18895289082469844767783102971904, coefficient := (-18895289082469844767783102971904) }, { argument := 217219791268356570111205703680, coefficient := (-217219791268356570111205703680) }, { argument := 8269052606164063554990243840, coefficient := (-8269052606164063554990243840) }, { argument := 209482666022822943393086177280, coefficient := (-209482666022822943393086177280) }, { argument := 8269052606164063554990243840, coefficient := (-8269052606164063554990243840) }, { argument := 217316505333925740445182197760, coefficient := (-217316505333925740445182197760) }, { argument := 210836662940791328068757094400, coefficient := (-210836662940791328068757094400) }, { argument := 138488550088309082967196565504, coefficient := (-138488550088309082967196565504) }, { argument := 5257090456296363324336601300992, coefficient := (-5257090456296363324336601300992) }, { argument := 7751293544020600444881469440, coefficient := (-7751293544020600444881469440) }, { argument := 194103284224298071505741836976128, coefficient := (-194103284224298071505741836976128) }, { argument := 61327554894646715549850009600, coefficient := (-61327554894646715549850009600) }, { argument := 7340131943986119772314009600, coefficient := (-7340131943986119772314009600) }, { argument := 194095567943803577034889354018816, coefficient := (-194095567943803577034889354018816) }, { argument := 7340556956969578040383242240, coefficient := (-7340556956969578040383242240) }, { argument := 7340556956969578040383242240, coefficient := (-7340556956969578040383242240) }, { argument := 314002026872485018104244469760, coefficient := (-314002026872485018104244469760) }, { argument := 7339281918019203236175544320, coefficient := (-7339281918019203236175544320) }, { argument := 61327554894646715549850009600, coefficient := (-61327554894646715549850009600) }, { argument := 314002026872485018104244469760, coefficient := (-314002026872485018104244469760) }, { argument := 5264807707099486540043158290432, coefficient := (-5264807707099486540043158290432) }, { argument := 7340131943986119772314009600, coefficient := (-7340131943986119772314009600) }, { argument := 7339281918019203236175544320, coefficient := (-7339281918019203236175544320) }, { argument := 7751293544020600444881469440, coefficient := (-7751293544020600444881469440) }, { argument := 363131093066744238352367616, coefficient := (-363131093066744238352367616) }, { argument := 355565861961187066720026624, coefficient := (-355565861961187066720026624) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 8798363775762990608412573696, coefficient := (-8798363775762990608412573696) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 287478782011172522028957696, coefficient := (-287478782011172522028957696) }, { argument := 287478782011172522028957696, coefficient := (-287478782011172522028957696) }, { argument := 4864443600873261359595257856, coefficient := (-4864443600873261359595257856) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 8798363775762990608412573696, coefficient := (-8798363775762990608412573696) }, { argument := 4864443600873261359595257856, coefficient := (-4864443600873261359595257856) }, { argument := 363131093066744238352367616, coefficient := (-363131093066744238352367616) }] }

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

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-48466833116574856750743768166039552)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    29637, 28035, 37647, 9355326990489523, 2403, 135,
    32814730235616077, 7299, 36544245784909, 7299, 7299, 2403,
    135, 135, 2115, 1665, 52335, 1665,
    1665, 855, 855, 28935, 1575, 52335,
    28935, 135, 1665, 1575, 2115, 405492655,
    37647, 2115, 11198800165, 114351, 3243940195, 114351,
    114351, 37647, 2115, 121607480433981, 121607445258947, 30504347568105,
    2097797661098451, 5615, 21616768357102705, 6305, 855, 5615,
    2725, 6305, 17675, 5415, 2097797851414995, 5615,
    855, 5415, 855, 11235, 2725, 30750626613225,
    65508011607624339, 11601041451, 1208803069818119737, 187193415171
  ]
def negativeCoefficients : Array ℕ := #[
    279913550905615350396616704, 264783088694501007131934720, 355565861961187066720026624, 5266580893537219944859540914176, 363131093066744238352367616, 20400623205996867323166720,
    18473050857672989098222261633024, 551496847335448646636273664, 5266580854382463728488596635648, 551496847335448646636273664, 551496847335448646636273664, 363131093066744238352367616,
    20400623205996867323166720, 20400623205996867323166720, 19975610222538599253934080, 15725480387955918561607680, 494290099761965764517560320, 15725480387955918561607680,
    15725480387955918561607680, 16150493371414186630840320, 16150493371414186630840320, 273283348363666368516587520, 14875454421039382423142400, 494290099761965764517560320,
    273283348363666368516587520, 20400623205996867323166720, 15725480387955918561607680, 14875454421039382423142400, 19975610222538599253934080, 7480019230554001783631380480,
    355565861961187066720026624, 19975610222538599253934080, 25822675072046412349917102080, 540007329682626799831351296, 7480016820948057155321200640, 540007329682626799831351296,
    540007329682626799831351296, 355565861961187066720026624, 19975610222538599253934080, 136917850891985428698988806144, 136917811288417924912856956928, 137379368340897773853427630080,
    18895281529643363952248217403392, 217219791268356570111205703680, 194706539836004142495848317583360, 121956436682723791144359034880, 8269052606164063554990243840, 217219791268356570111205703680,
    210836662940791328068757094400, 121956436682723791144359034880, 2735073774296137044855252582400, 209482666022822943393086177280, 18895283243862397233929429975040, 217219791268356570111205703680,
    8269052606164063554990243840, 209482666022822943393086177280, 8269052606164063554990243840, 217316505333925740445182197760, 210836662940791328068757094400, 138488510556729367424768409600,
    18438866041617443734068746256384, 26750180329386638453980004352, 680495631849649463443734023634944, 215819313871443495107633872896
  ]
def negativeScales : Array ℕ := #[
    14, 14, 15, 53, 11, 7,
    54, 12, 45, 12, 12, 11,
    7, 7, 11, 10, 15, 10,
    10, 9, 9, 14, 10, 15,
    14, 7, 10, 10, 11, 28,
    15, 11, 33, 16, 31, 16,
    16, 15, 11, 46, 46, 44,
    50, 12, 54, 12, 9, 12,
    11, 12, 14, 12, 50, 12,
    9, 12, 9, 13, 11, 44,
    55, 33, 60, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14855111799946705, 14774941449737867, 15200247284086348, 53054709503212970, 11230620933129867, 7076815597050831,
    54865193093502498, 12833483106919052, 45054709492487154, 12833483106919052, 12833483106919052, 11230620933129867,
    7076815597050831, 7076815597050831, 11046441948007313, 10701306462033270, 15675488477843117, 10701306462033270,
    10701306462033270, 9739780609952834, 9739780609952834, 14820528024633809, 10621136113284685, 15675488477843117,
    14820528024633809, 7076815597050831, 10701306462033270, 10621136113284685, 11046441948007313, 28595100541139362,
    15200247284086348, 11046441948007313, 33382625119662740, 16803109457304290, 31595100076390943, 16803109457304290,
    16803109457304290, 15200247284086348, 11046441948007313, 46789225304869383, 46789224887568944, 44794080108519824,
    50897796959853153, 12455070307288020, 54263000378751275, 12622280655225937, 9739780609952834, 12455070307288020,
    11412040514551662, 12622280655225937, 14109422594584124, 12402745622495697, 50897797090737436, 12455070307288020,
    9739780609952834, 12402745622495697, 9739780609952834, 13455712504067328, 11412040514551662, 44805681043170568,
    55862520878948372, 33433535273946308, 60068284937391471, 37445738730459969
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
noncomputable def negativeCeiling : ℝ := 337181100607 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 355565861961187066720026624, coefficient := (-355565861961187066720026624) }, { argument := 5266580893537219944859540914176, coefficient := (-5266580893537219944859540914176) }, { argument := 363131093066744238352367616, coefficient := (-363131093066744238352367616) }, { argument := 20400623205996867323166720, coefficient := (-20400623205996867323166720) }, { argument := 18473050857672989098222261633024, coefficient := (-18473050857672989098222261633024) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 5266580854382463728488596635648, coefficient := (-5266580854382463728488596635648) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 363131093066744238352367616, coefficient := (-363131093066744238352367616) }, { argument := 20400623205996867323166720, coefficient := (-20400623205996867323166720) }, { argument := 20400623205996867323166720, coefficient := (-20400623205996867323166720) }, { argument := 19975610222538599253934080, coefficient := (-19975610222538599253934080) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 494290099761965764517560320, coefficient := (-494290099761965764517560320) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 16150493371414186630840320, coefficient := (-16150493371414186630840320) }, { argument := 16150493371414186630840320, coefficient := (-16150493371414186630840320) }, { argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 494290099761965764517560320, coefficient := (-494290099761965764517560320) }, { argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 20400623205996867323166720, coefficient := (-20400623205996867323166720) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 19975610222538599253934080, coefficient := (-19975610222538599253934080) }, { argument := 7480019230554001783631380480, coefficient := (-7480019230554001783631380480) }, { argument := 355565861961187066720026624, coefficient := (-355565861961187066720026624) }, { argument := 19975610222538599253934080, coefficient := (-19975610222538599253934080) }, { argument := 25822675072046412349917102080, coefficient := (-25822675072046412349917102080) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 7480016820948057155321200640, coefficient := (-7480016820948057155321200640) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 355565861961187066720026624, coefficient := (-355565861961187066720026624) }, { argument := 19975610222538599253934080, coefficient := (-19975610222538599253934080) }, { argument := 136917850891985428698988806144, coefficient := (-136917850891985428698988806144) }, { argument := 136917811288417924912856956928, coefficient := (-136917811288417924912856956928) }, { argument := 137379368340897773853427630080, coefficient := (-137379368340897773853427630080) }, { argument := 18895281529643363952248217403392, coefficient := (-18895281529643363952248217403392) }, { argument := 217219791268356570111205703680, coefficient := (-217219791268356570111205703680) }, { argument := 194706539836004142495848317583360, coefficient := (-194706539836004142495848317583360) }, { argument := 121956436682723791144359034880, coefficient := (-121956436682723791144359034880) }, { argument := 8269052606164063554990243840, coefficient := (-8269052606164063554990243840) }, { argument := 217219791268356570111205703680, coefficient := (-217219791268356570111205703680) }, { argument := 210836662940791328068757094400, coefficient := (-210836662940791328068757094400) }, { argument := 121956436682723791144359034880, coefficient := (-121956436682723791144359034880) }, { argument := 2735073774296137044855252582400, coefficient := (-2735073774296137044855252582400) }, { argument := 209482666022822943393086177280, coefficient := (-209482666022822943393086177280) }, { argument := 18895283243862397233929429975040, coefficient := (-18895283243862397233929429975040) }, { argument := 217219791268356570111205703680, coefficient := (-217219791268356570111205703680) }, { argument := 8269052606164063554990243840, coefficient := (-8269052606164063554990243840) }, { argument := 209482666022822943393086177280, coefficient := (-209482666022822943393086177280) }, { argument := 8269052606164063554990243840, coefficient := (-8269052606164063554990243840) }, { argument := 217316505333925740445182197760, coefficient := (-217316505333925740445182197760) }, { argument := 210836662940791328068757094400, coefficient := (-210836662940791328068757094400) }, { argument := 138488510556729367424768409600, coefficient := (-138488510556729367424768409600) }, { argument := 18438866041617443734068746256384, coefficient := (-18438866041617443734068746256384) }, { argument := 26750180329386638453980004352, coefficient := (-26750180329386638453980004352) }, { argument := 680495631849649463443734023634944, coefficient := (-680495631849649463443734023634944) }, { argument := 215819313871443495107633872896, coefficient := (-215819313871443495107633872896) }] }

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

end TermShard1


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
