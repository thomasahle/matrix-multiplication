import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 0, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-184212833737524418480277865627648)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    19, 643, 643, 643, 643, 1976902443,
    9574210773, 1976902443, 35, 35, 35, 35,
    1124120997, 5444159067, 1124120997, 39899015, 3340710009, 1670355609,
    19948903, 1163, 1163, 1163, 1163, 2028586167,
    9824516937, 2028586167, 643, 643, 643, 643,
    31669201881, 153375101991, 31669201881, 1867531315, 156366781389, 78183418989,
    933737363, 38762793, 187729623, 38762793, 508390675, 42567111405,
    21283563405, 254187635, 43848021, 4597385919, 49555225125, 2298694713,
    43848021, 724021221, 670424091, 724021221, 670424091, 1508882255,
    9523163811, 25998236111, 15339706977, 475207775, 15339706977, 10245479629,
    763945283, 9523163811, 57024933, 1909052535
  ]
def negativeCoefficients : Array ℕ := #[
    183756724581423634555338752, 3109357208048826237344284672, 3109357208048826237344284672, 3109357208048826237344284672, 3109357208048826237344284672, 2279213339044511541381562368,
    22076626979660486894363344896, 2279213339044511541381562368, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640,
    1296023271221388915687555072, 12553376125689296469343862784, 1296023271221388915687555072, 184001729624524626392514560, 15406305640125733210618331136, 15406311215654129489330307072,
    183996154096128347680538624, 5623922912847254920733130752, 5623922912847254920733130752, 5623922912847254920733130752, 5623922912847254920733130752, 2338800615882276548999380992,
    22653793698082983283758465024, 2338800615882276548999380992, 3109357208048826237344284672, 3109357208048826237344284672, 3109357208048826237344284672, 3109357208048826237344284672,
    36512103882340508417818361856, 353658906713384662601859858432, 36512103882340508417818361856, 8612468054360813964372213760, 721114499478143189955070918656, 721114760448843286742525018112,
    8612207083660717176918114304, 1430094644106360182827646976, 13852001242139913345482883072, 1430094644106360182827646976, 2344538167796362175001395200, 196306152511279503812717445120,
    196306223554302617686628106240, 2344467124773248301090734080, 202213305381410491789737984, 21201700363967247673800523776, 228533138848984106048421888000, 21201716537150114298649903104,
    202213305381410491789737984, 1669479270965212945047355392, 1545892703440795392521797632, 1669479270965212945047355392, 1545892703440795392521797632, 3479245599418344307173621760,
    21958920699191189809315971072, 59947850988436363818588700672, 35370956096301976399437103104, 1095754525907744002460876800, 35370956096301976399437103104, 23624467578570960693056503808,
    3523075780454654067272056832, 21958920699191189809315971072, 1051924344871434242362441728, 17607901768205723183119073280
  ]
def negativeScales : Array ℕ := #[
    4, 9, 9, 9, 9, 30,
    33, 30, 5, 5, 5, 5,
    30, 32, 30, 25, 31, 30,
    24, 10, 10, 10, 10, 30,
    33, 30, 9, 9, 9, 9,
    34, 37, 34, 30, 37, 36,
    29, 25, 27, 25, 28, 35,
    34, 27, 25, 32, 35, 31,
    25, 29, 29, 29, 29, 30,
    33, 34, 33, 28, 33, 33,
    29, 33, 25, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    4247927513443586, 9328674927327948, 9328674927327948, 9328674927327948, 9328674927327948, 30880594535169351,
    33156506420835116, 30880594535169351, 5129283016944967, 5129283016944967, 5129283016944967, 5129283016944967,
    30066150185254063, 32342062073991193, 30066150185254063, 25249849794815646, 31637507608678382, 30637508130788348,
    24249806078329632, 10183635381473219, 10183635381473219, 10183635381473219, 10183635381473219, 30917827444288710,
    33193739327034091, 30917827444288710, 9328674927327948, 9328674927327948, 9328674927327948, 9328674927327948,
    34882361461444715, 37158273347009304, 34882361461444715, 30798485289121883, 37186143102342797, 36186143624452763,
    29798441572635311, 25208169190126491, 27484081078863778, 25208169190126491, 28921362333867493, 35309020141340518,
    34309020663450484, 27921318617376613, 25386008394956471, 32098166629572912, 35528318132713771, 31098167730096050,
    25386008394956471, 29431456742295235, 29320498750829724, 29431456742295235, 29320498750829724, 30490833084135159,
    33148793803166018, 34597694693661992, 33836551874585567, 28823983200790806, 33836551874585567, 33254268472723315,
    29508894069125350, 33148793803166018, 25765089511003600, 30830209659816870
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
noncomputable def negativeCeiling : ℝ := 627367191 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 2279213339044511541381562368, coefficient := (-2279213339044511541381562368) }, { argument := 22076626979660486894363344896, coefficient := (-22076626979660486894363344896) }, { argument := 2279213339044511541381562368, coefficient := (-2279213339044511541381562368) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 1296023271221388915687555072, coefficient := (-1296023271221388915687555072) }, { argument := 12553376125689296469343862784, coefficient := (-12553376125689296469343862784) }, { argument := 1296023271221388915687555072, coefficient := (-1296023271221388915687555072) }, { argument := 184001729624524626392514560, coefficient := (-184001729624524626392514560) }, { argument := 15406305640125733210618331136, coefficient := (-15406305640125733210618331136) }, { argument := 15406311215654129489330307072, coefficient := (-15406311215654129489330307072) }, { argument := 183996154096128347680538624, coefficient := (-183996154096128347680538624) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 2338800615882276548999380992, coefficient := (-2338800615882276548999380992) }, { argument := 22653793698082983283758465024, coefficient := (-22653793698082983283758465024) }, { argument := 2338800615882276548999380992, coefficient := (-2338800615882276548999380992) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 3109357208048826237344284672, coefficient := (-3109357208048826237344284672) }, { argument := 36512103882340508417818361856, coefficient := (-36512103882340508417818361856) }, { argument := 353658906713384662601859858432, coefficient := (-353658906713384662601859858432) }, { argument := 36512103882340508417818361856, coefficient := (-36512103882340508417818361856) }, { argument := 8612468054360813964372213760, coefficient := (-8612468054360813964372213760) }, { argument := 721114499478143189955070918656, coefficient := (-721114499478143189955070918656) }, { argument := 721114760448843286742525018112, coefficient := (-721114760448843286742525018112) }, { argument := 8612207083660717176918114304, coefficient := (-8612207083660717176918114304) }, { argument := 1430094644106360182827646976, coefficient := (-1430094644106360182827646976) }, { argument := 13852001242139913345482883072, coefficient := (-13852001242139913345482883072) }, { argument := 1430094644106360182827646976, coefficient := (-1430094644106360182827646976) }, { argument := 2344538167796362175001395200, coefficient := (-2344538167796362175001395200) }, { argument := 196306152511279503812717445120, coefficient := (-196306152511279503812717445120) }, { argument := 196306223554302617686628106240, coefficient := (-196306223554302617686628106240) }, { argument := 2344467124773248301090734080, coefficient := (-2344467124773248301090734080) }, { argument := 202213305381410491789737984, coefficient := (-202213305381410491789737984) }, { argument := 21201700363967247673800523776, coefficient := (-21201700363967247673800523776) }, { argument := 228533138848984106048421888000, coefficient := (-228533138848984106048421888000) }, { argument := 21201716537150114298649903104, coefficient := (-21201716537150114298649903104) }, { argument := 202213305381410491789737984, coefficient := (-202213305381410491789737984) }, { argument := 1669479270965212945047355392, coefficient := (-1669479270965212945047355392) }, { argument := 1545892703440795392521797632, coefficient := (-1545892703440795392521797632) }, { argument := 1669479270965212945047355392, coefficient := (-1669479270965212945047355392) }, { argument := 1545892703440795392521797632, coefficient := (-1545892703440795392521797632) }, { argument := 3479245599418344307173621760, coefficient := (-3479245599418344307173621760) }, { argument := 21958920699191189809315971072, coefficient := (-21958920699191189809315971072) }, { argument := 59947850988436363818588700672, coefficient := (-59947850988436363818588700672) }, { argument := 35370956096301976399437103104, coefficient := (-35370956096301976399437103104) }, { argument := 1095754525907744002460876800, coefficient := (-1095754525907744002460876800) }, { argument := 35370956096301976399437103104, coefficient := (-35370956096301976399437103104) }, { argument := 23624467578570960693056503808, coefficient := (-23624467578570960693056503808) }, { argument := 3523075780454654067272056832, coefficient := (-3523075780454654067272056832) }, { argument := 21958920699191189809315971072, coefficient := (-21958920699191189809315971072) }, { argument := 1051924344871434242362441728, coefficient := (-1051924344871434242362441728) }, { argument := 17607901768205723183119073280, coefficient := (-17607901768205723183119073280) }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-327903127546830424216400195223552)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1939767453, 1885885365, 1670355609, 78183418989, 21283563405, 484941951,
    78183418989, 1885885365, 1885885365, 808236585, 1885885365, 21283563405,
    808236585, 1909051833, 1670355609, 1976902443, 9574210773, 1976902443,
    1867531315, 156366781389, 78183418989, 933737363, 282193631, 13279727579,
    5319005985, 41679670675, 5458064965, 173823725, 5319005985, 3024532815,
    5458064965, 85208389995, 104294235, 6639866733, 5319005985, 173823725,
    104294235, 173823725, 2676885365, 3024532815, 282193631, 45047275,
    3771769365, 1885885365, 22522955, 70629447, 7405370133, 79822488375,
    3702687891, 70629447, 623363275, 10908080225, 10908085575, 623357925,
    37, 37, 37, 37, 64604655, 312882705,
    64604655, 35, 35, 35
  ]
def negativeCoefficients : Array ℕ := #[
    35782393768002421199940354048, 17394222340254662326663249920, 15406311215654129489330307072, 721114760448843286742525018112, 196306223554302617686628106240, 35782400242809591071992971264,
    721114760448843286742525018112, 17394222340254662326663249920, 17394222340254662326663249920, 14909333434503996279997071360, 17394222340254662326663249920, 196306223554302617686628106240,
    14909333434503996279997071360, 17607895293398553311066456064, 15406311215654129489330307072, 2279213339044511541381562368, 22076626979660486894363344896, 2279213339044511541381562368,
    8612468054360813964372213760, 721114499478143189955070918656, 721114760448843286742525018112, 8612207083660717176918114304, 1301388422571957502475239424, 61241934004598885357679804416,
    24529585532956096549292605440, 384427109009111018478397030400, 25170881886758870315287183360, 801620442253467207493222400, 24529585532956096549292605440, 13948195695210329410382069760,
    25170881886758870315287183360, 392954340792649625113177620480, 15391112491266570383869870080, 61241961153594475839712395264, 24529585532956096549292605440, 801620442253467207493222400,
    15391112491266570383869870080, 801620442253467207493222400, 24689909621406789990791249920, 13948195695210329410382069760, 1301388422571957502475239424, 207743888285753610443161600,
    17394216045303247173278760960, 17394222340254662326663249920, 207737593334338457058672640, 325720833219158217314009088, 34151241903635866013487071232, 368116253595070206748655616000,
    34151267955050184109801340928, 325720833219158217314009088, 1437377849859303436766412800, 50304641061516775594026598400, 50304665734036974180551884800, 1437365513599204143503769600,
    178921021302965117856514048, 178921021302965117856514048, 178921021302965117856514048, 178921021302965117856514048, 74484096047206259522273280, 721458398028120486743900160,
    74484096047206259522273280, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640
  ]
def negativeScales : Array ℕ := #[
    30, 30, 30, 36, 34, 28,
    36, 30, 30, 29, 30, 34,
    29, 30, 30, 30, 33, 30,
    30, 37, 36, 29, 28, 33,
    32, 35, 32, 27, 32, 31,
    32, 36, 26, 32, 32, 27,
    26, 27, 31, 31, 28, 25,
    31, 30, 24, 26, 32, 36,
    31, 26, 29, 33, 33, 29,
    5, 5, 5, 5, 25, 28,
    25, 5, 5, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30853236562615643, 30812594838164344, 30637508130788348, 36186143624452763, 34309020663450484, 28853236823670612,
    36186143624452763, 30812594838164344, 30812594838164344, 29590202415998839, 30812594838164344, 34309020663450484,
    29590202415998839, 30830209129306520, 30637508130788348, 30880594535169351, 33156506420835116, 30880594535169351,
    30798485289121883, 37186143102342797, 36186143624452763, 29798441572635311, 28072110186338097, 33628506500355543,
    32308509514280166, 35278624827319667, 32345742420479142, 27373049766474878, 32308509514280166, 31494065167436464,
    32345742420479142, 36310276440454354, 26636084172323563, 32628507139912625, 32308509514280166, 27373049766474878,
    26636084172323563, 27373049766474878, 31317908212282416, 31494065167436464, 28072110186338097, 25424936501373755,
    31812594316054369, 30812594838164344, 24424892784887741, 26073766465039040, 32785924700139021, 36216076202795663,
    31785925800662170, 26073766465039040, 29215497921222795, 33344678164780696, 33344678872367771, 29215485539274900,
    5209453365628950, 5209453365628950, 5209453365628950, 5209453365628950, 25945134793892351, 28221046673029826,
    25945134793892351, 5129283016944967, 5129283016944967, 5129283016944967
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
noncomputable def negativeCeiling : ℝ := 139359323 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 35782393768002421199940354048, coefficient := (-35782393768002421199940354048) }, { argument := 17394222340254662326663249920, coefficient := (-17394222340254662326663249920) }, { argument := 15406311215654129489330307072, coefficient := (-15406311215654129489330307072) }, { argument := 721114760448843286742525018112, coefficient := (-721114760448843286742525018112) }, { argument := 196306223554302617686628106240, coefficient := (-196306223554302617686628106240) }, { argument := 35782400242809591071992971264, coefficient := (-35782400242809591071992971264) }, { argument := 721114760448843286742525018112, coefficient := (-721114760448843286742525018112) }, { argument := 17394222340254662326663249920, coefficient := (-17394222340254662326663249920) }, { argument := 17394222340254662326663249920, coefficient := (-17394222340254662326663249920) }, { argument := 14909333434503996279997071360, coefficient := (-14909333434503996279997071360) }, { argument := 17394222340254662326663249920, coefficient := (-17394222340254662326663249920) }, { argument := 196306223554302617686628106240, coefficient := (-196306223554302617686628106240) }, { argument := 14909333434503996279997071360, coefficient := (-14909333434503996279997071360) }, { argument := 17607895293398553311066456064, coefficient := (-17607895293398553311066456064) }, { argument := 15406311215654129489330307072, coefficient := (-15406311215654129489330307072) }, { argument := 2279213339044511541381562368, coefficient := (-2279213339044511541381562368) }, { argument := 22076626979660486894363344896, coefficient := (-22076626979660486894363344896) }, { argument := 2279213339044511541381562368, coefficient := (-2279213339044511541381562368) }, { argument := 8612468054360813964372213760, coefficient := (-8612468054360813964372213760) }, { argument := 721114499478143189955070918656, coefficient := (-721114499478143189955070918656) }, { argument := 721114760448843286742525018112, coefficient := (-721114760448843286742525018112) }, { argument := 8612207083660717176918114304, coefficient := (-8612207083660717176918114304) }, { argument := 1301388422571957502475239424, coefficient := (-1301388422571957502475239424) }, { argument := 61241934004598885357679804416, coefficient := (-61241934004598885357679804416) }, { argument := 24529585532956096549292605440, coefficient := (-24529585532956096549292605440) }, { argument := 384427109009111018478397030400, coefficient := (-384427109009111018478397030400) }, { argument := 25170881886758870315287183360, coefficient := (-25170881886758870315287183360) }, { argument := 801620442253467207493222400, coefficient := (-801620442253467207493222400) }, { argument := 24529585532956096549292605440, coefficient := (-24529585532956096549292605440) }, { argument := 13948195695210329410382069760, coefficient := (-13948195695210329410382069760) }, { argument := 25170881886758870315287183360, coefficient := (-25170881886758870315287183360) }, { argument := 392954340792649625113177620480, coefficient := (-392954340792649625113177620480) }, { argument := 15391112491266570383869870080, coefficient := (-15391112491266570383869870080) }, { argument := 61241961153594475839712395264, coefficient := (-61241961153594475839712395264) }, { argument := 24529585532956096549292605440, coefficient := (-24529585532956096549292605440) }, { argument := 801620442253467207493222400, coefficient := (-801620442253467207493222400) }, { argument := 15391112491266570383869870080, coefficient := (-15391112491266570383869870080) }, { argument := 801620442253467207493222400, coefficient := (-801620442253467207493222400) }, { argument := 24689909621406789990791249920, coefficient := (-24689909621406789990791249920) }, { argument := 13948195695210329410382069760, coefficient := (-13948195695210329410382069760) }, { argument := 1301388422571957502475239424, coefficient := (-1301388422571957502475239424) }, { argument := 207743888285753610443161600, coefficient := (-207743888285753610443161600) }, { argument := 17394216045303247173278760960, coefficient := (-17394216045303247173278760960) }, { argument := 17394222340254662326663249920, coefficient := (-17394222340254662326663249920) }, { argument := 207737593334338457058672640, coefficient := (-207737593334338457058672640) }, { argument := 325720833219158217314009088, coefficient := (-325720833219158217314009088) }, { argument := 34151241903635866013487071232, coefficient := (-34151241903635866013487071232) }, { argument := 368116253595070206748655616000, coefficient := (-368116253595070206748655616000) }, { argument := 34151267955050184109801340928, coefficient := (-34151267955050184109801340928) }, { argument := 325720833219158217314009088, coefficient := (-325720833219158217314009088) }, { argument := 1437377849859303436766412800, coefficient := (-1437377849859303436766412800) }, { argument := 50304641061516775594026598400, coefficient := (-50304641061516775594026598400) }, { argument := 50304665734036974180551884800, coefficient := (-50304665734036974180551884800) }, { argument := 1437365513599204143503769600, coefficient := (-1437365513599204143503769600) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 74484096047206259522273280, coefficient := (-74484096047206259522273280) }, { argument := 721458398028120486743900160, coefficient := (-721458398028120486743900160) }, { argument := 74484096047206259522273280, coefficient := (-74484096047206259522273280) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0
