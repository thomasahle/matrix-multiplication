import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2585755476093123661596989352574976)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    38465, 5495, 51653, 609945, 42861, 38465,
    609945, 5495, 42861, 42861, 42861, 42861,
    42861, 49455, 51653, 14331214037707, 7352719058950601, 305235,
    77558966252513235, 313215, 9975, 305235, 173565, 313215,
    4889745, 5985, 1838180279755267, 305235, 9975, 5985,
    9975, 153615, 173565, 14331209521867, 1575, 1225,
    175, 1645, 19425, 1365, 1225, 19425,
    175, 1365, 1365, 1365, 1365, 1365,
    1575, 1645, 32796145, 3372978725, 43605, 119765639375,
    44745, 1425, 43605, 24795, 44745, 698535,
    855, 3372978725, 43605, 1425
  ]
def negativeCoefficients : Array ℕ := #[
    1453166614108647225158533120, 1660761844695596828752609280, 1951395167517326273784315904, 23043070595151405998942453760, 51815769554502621057081409536, 1453166614108647225158533120,
    23043070595151405998942453760, 1660761844695596828752609280, 1619242798578206908033794048, 1619242798578206908033794048, 1619242798578206908033794048, 51815769554502621057081409536,
    1619242798578206908033794048, 1868357075282546432346685440, 1951395167517326273784315904, 32271025099992033305701646336, 4139212851756233834436348608512, 1441431533398716156802498560,
    43661816439257434964906811064320, 1479116017932015925607792640, 47105605666624711006617600, 1441431533398716156802498560, 819637538599269971515146240, 1479116017932015925607792640,
    23091167897779433335443947520, 904427628799194451327057920, 4139214011472807276706808201216, 1441431533398716156802498560, 47105605666624711006617600, 904427628799194451327057920,
    47105605666624711006617600, 1450852654532041099003822080, 819637538599269971515146240, 32271014931224362673311318016, 59501817684157529692569600, 46279191532122523094220800,
    52890504608140026393395200, 62146342914564531012239360, 733855751437942866208358400, 1650183743773968823473930240, 46279191532122523094220800, 733855751437942866208358400,
    52890504608140026393395200, 51568241992936525733560320, 51568241992936525733560320, 51568241992936525733560320, 1650183743773968823473930240, 51568241992936525733560320,
    59501817684157529692569600, 62146342914564531012239360, 151245523354817285670830080, 15555118826535537357514342400, 1647350323884247036345712640, 138080381148426036083425280000,
    1690418306208018200694620160, 53834977904713955436134400, 1647350323884247036345712640, 936728615542022824588738560, 1690418306208018200694620160, 26389906168890780954793082880,
    1033631575770507944373780480, 15555118826535537357514342400, 1647350323884247036345712640, 53834977904713955436134400
  ]
def negativeScales : Array ℕ := #[
    15, 12, 15, 19, 15, 15,
    19, 12, 15, 15, 15, 15,
    15, 15, 15, 43, 52, 18,
    56, 18, 13, 18, 17, 18,
    22, 12, 50, 18, 13, 12,
    13, 17, 17, 43, 10, 10,
    7, 10, 14, 10, 10, 14,
    7, 10, 10, 10, 10, 10,
    10, 10, 24, 31, 15, 36,
    15, 10, 15, 14, 15, 19,
    9, 31, 15, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15231258687894198, 12423903765836611, 15656564522652026, 19218319632186700, 15387377889811484, 15231258687894198,
    19218319632186700, 12423903765836611, 15387377889811484, 15387377889811484, 15387377889811484, 15387377889811484,
    15387377889811484, 15593828767283669, 15656564522652026, 43704226063173170, 52707199285242729, 18219560873802360,
    56106143092757619, 18256793780001336, 13284101125997071, 18219560873802360, 17405116526958445, 18256793780001336,
    22221327799976548, 12547135531832084, 50707199689454152, 18219560873802360, 13284101125997071, 12547135531832084,
    13284101125997071, 17228959571804610, 17405116526958445, 43704225608572395, 10621136113284685, 10258566033889934,
    7451211111832378, 10683871868671904, 14245626978182435, 10414685235807227, 10258566033889934, 14245626978182435,
    7451211111832378, 10414685235807227, 10414685235807227, 10414685235807227, 10414685235807227, 10414685235807227,
    10621136113284685, 10683871868671904, 24967022922294076, 31651376072621171, 15412205951744767, 36801423104358473,
    15449438857943777, 10476746203939589, 15412205951744767, 14597761604906147, 15449438857943777, 19413972877918956,
    9739780609952834, 31651376072621171, 15412205951744767, 10476746203939589
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
noncomputable def negativeCeiling : ℝ := 4349665063 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1453166614108647225158533120, coefficient := (-1453166614108647225158533120) }, { argument := 1660761844695596828752609280, coefficient := (-1660761844695596828752609280) }, { argument := 1951395167517326273784315904, coefficient := (-1951395167517326273784315904) }, { argument := 23043070595151405998942453760, coefficient := (-23043070595151405998942453760) }, { argument := 51815769554502621057081409536, coefficient := (-51815769554502621057081409536) }, { argument := 1453166614108647225158533120, coefficient := (-1453166614108647225158533120) }, { argument := 23043070595151405998942453760, coefficient := (-23043070595151405998942453760) }, { argument := 1660761844695596828752609280, coefficient := (-1660761844695596828752609280) }, { argument := 1619242798578206908033794048, coefficient := (-1619242798578206908033794048) }, { argument := 1619242798578206908033794048, coefficient := (-1619242798578206908033794048) }, { argument := 1619242798578206908033794048, coefficient := (-1619242798578206908033794048) }, { argument := 51815769554502621057081409536, coefficient := (-51815769554502621057081409536) }, { argument := 1619242798578206908033794048, coefficient := (-1619242798578206908033794048) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 1951395167517326273784315904, coefficient := (-1951395167517326273784315904) }, { argument := 32271025099992033305701646336, coefficient := (-32271025099992033305701646336) }, { argument := 4139212851756233834436348608512, coefficient := (-4139212851756233834436348608512) }, { argument := 1441431533398716156802498560, coefficient := (-1441431533398716156802498560) }, { argument := 43661816439257434964906811064320, coefficient := (-43661816439257434964906811064320) }, { argument := 1479116017932015925607792640, coefficient := (-1479116017932015925607792640) }, { argument := 47105605666624711006617600, coefficient := (-47105605666624711006617600) }, { argument := 1441431533398716156802498560, coefficient := (-1441431533398716156802498560) }, { argument := 819637538599269971515146240, coefficient := (-819637538599269971515146240) }, { argument := 1479116017932015925607792640, coefficient := (-1479116017932015925607792640) }, { argument := 23091167897779433335443947520, coefficient := (-23091167897779433335443947520) }, { argument := 904427628799194451327057920, coefficient := (-904427628799194451327057920) }, { argument := 4139214011472807276706808201216, coefficient := (-4139214011472807276706808201216) }, { argument := 1441431533398716156802498560, coefficient := (-1441431533398716156802498560) }, { argument := 47105605666624711006617600, coefficient := (-47105605666624711006617600) }, { argument := 904427628799194451327057920, coefficient := (-904427628799194451327057920) }, { argument := 47105605666624711006617600, coefficient := (-47105605666624711006617600) }, { argument := 1450852654532041099003822080, coefficient := (-1450852654532041099003822080) }, { argument := 819637538599269971515146240, coefficient := (-819637538599269971515146240) }, { argument := 32271014931224362673311318016, coefficient := (-32271014931224362673311318016) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 46279191532122523094220800, coefficient := (-46279191532122523094220800) }, { argument := 52890504608140026393395200, coefficient := (-52890504608140026393395200) }, { argument := 62146342914564531012239360, coefficient := (-62146342914564531012239360) }, { argument := 733855751437942866208358400, coefficient := (-733855751437942866208358400) }, { argument := 1650183743773968823473930240, coefficient := (-1650183743773968823473930240) }, { argument := 46279191532122523094220800, coefficient := (-46279191532122523094220800) }, { argument := 733855751437942866208358400, coefficient := (-733855751437942866208358400) }, { argument := 52890504608140026393395200, coefficient := (-52890504608140026393395200) }, { argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 1650183743773968823473930240, coefficient := (-1650183743773968823473930240) }, { argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 62146342914564531012239360, coefficient := (-62146342914564531012239360) }, { argument := 151245523354817285670830080, coefficient := (-151245523354817285670830080) }, { argument := 15555118826535537357514342400, coefficient := (-15555118826535537357514342400) }, { argument := 1647350323884247036345712640, coefficient := (-1647350323884247036345712640) }, { argument := 138080381148426036083425280000, coefficient := (-138080381148426036083425280000) }, { argument := 1690418306208018200694620160, coefficient := (-1690418306208018200694620160) }, { argument := 53834977904713955436134400, coefficient := (-53834977904713955436134400) }, { argument := 1647350323884247036345712640, coefficient := (-1647350323884247036345712640) }, { argument := 936728615542022824588738560, coefficient := (-936728615542022824588738560) }, { argument := 1690418306208018200694620160, coefficient := (-1690418306208018200694620160) }, { argument := 26389906168890780954793082880, coefficient := (-26389906168890780954793082880) }, { argument := 1033631575770507944373780480, coefficient := (-1033631575770507944373780480) }, { argument := 15555118826535537357514342400, coefficient := (-15555118826535537357514342400) }, { argument := 1647350323884247036345712640, coefficient := (-1647350323884247036345712640) }, { argument := 53834977904713955436134400, coefficient := (-53834977904713955436134400) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-70011805585605493470013803200512)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    855, 1425, 21945, 24795, 131176005, 2142048831663,
    77714843071057, 621716431139033, 17138707511079, 48195, 37485, 5355,
    50337, 594405, 41769, 37485, 594405, 5355,
    41769, 41769, 41769, 41769, 41769, 48195,
    50337, 27405, 21315, 3045, 28623, 337995,
    23751, 21315, 337995, 3045, 23751, 23751,
    23751, 23751, 23751, 27405, 28623, 33100421,
    3095559625, 409887, 106091645755, 420603, 13395, 409887,
    233073, 420603, 6566229, 8037, 3095559625, 409887,
    13395, 8037, 13395, 206283, 233073, 132394089,
    49455, 38465, 5495, 51653
  ]
def negativeCoefficients : Array ℕ := #[
    1033631575770507944373780480, 53834977904713955436134400, 1658117319465189827432939520, 936728615542022824588738560, 151235637052915281958010880, 9646930320086893113636814848,
    349996538295968878194193334272, 349995235950982956851497271296, 9648234595063413168194715648, 1820755621135220408592629760, 1416143260882949206683156480, 1618449441009084807637893120,
    1901678093185674648974524416, 22455985994001051705975767040, 50495622559483445998302265344, 1416143260882949206683156480, 22455985994001051705975767040, 1618449441009084807637893120,
    1577988204983857687446945792, 1577988204983857687446945792, 1577988204983857687446945792, 50495622559483445998302265344, 1577988204983857687446945792, 1820755621135220408592629760,
    1901678093185674648974524416, 1035331627704341016650711040, 805257932658931901839441920, 920294780181636459245076480, 1081346366713422839612964864, 12769090075020205872025436160,
    28713197141667057528446386176, 805257932658931901839441920, 12769090075020205872025436160, 920294780181636459245076480, 897287410677095547763949568, 897287410677095547763949568,
    897287410677095547763949568, 28713197141667057528446386176, 897287410677095547763949568, 1035331627704341016650711040, 1081346366713422839612964864, 152648748729760297552707584,
    14275749041820827989835776000, 1935636630563990267706212352, 122315339850071209925284986880, 1986241509794421385816178688, 63256099038038897637457920, 1935636630563990267706212352,
    1100656123261876818891767808, 1986241509794421385816178688, 31008139748446667621881872384, 1214517101530346834639192064, 14275749041820827989835776000, 1935636630563990267706212352,
    63256099038038897637457920, 1214517101530346834639192064, 63256099038038897637457920, 1948287850371598047233703936, 1100656123261876818891767808, 152639992290932808549924864,
    1868357075282546432346685440, 1453166614108647225158533120, 1660761844695596828752609280, 1951395167517326273784315904
  ]
def negativeScales : Array ℕ := #[
    9, 10, 14, 14, 26, 40,
    46, 49, 43, 15, 15, 12,
    15, 19, 15, 15, 19, 12,
    15, 15, 15, 15, 15, 15,
    15, 14, 14, 11, 14, 18,
    14, 14, 18, 11, 14, 14,
    14, 14, 14, 14, 14, 24,
    31, 18, 36, 18, 13, 18,
    17, 18, 22, 12, 31, 18,
    13, 12, 13, 17, 17, 26,
    15, 15, 12, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    9739780609952834, 10476746203939589, 14421604649747022, 14597761604906147, 26966928616109969, 40962128520584615,
    46143255404625580, 49143250036314917, 43962323561306219, 15556595861081553, 15194025781695223, 12386670859637623,
    15619331616437464, 19181086725987725, 15350144983612506, 15194025781695223, 19181086725987725, 12386670859637623,
    15350144983612506, 15350144983612506, 15350144983612506, 15350144983612506, 15350144983612506, 15556595861081553,
    15619331616437464, 14742151514425259, 14379581434851302, 11572226512796267, 14804887270297456, 18366642379143803,
    14535700636769438, 14379581434851302, 18366642379143803, 11572226512796267, 14535700636769438, 14535700636769438,
    14535700636769438, 14535700636769438, 14535700636769438, 14742151514425259, 14804887270297456, 24980346248060028,
    31527553101949431, 18644866708553718, 36626520098683453, 18682099614781241, 13709406960819918, 18644866708553718,
    17830422362877459, 18682099614781241, 22646633634728772, 12972441381715804, 31527553101949431, 18644866708553718,
    13709406960819918, 12972441381715804, 13709406960819918, 17654265406561020, 17830422362877459, 26980263487887587,
    15593828767283669, 15231258687894198, 12423903765836611, 15656564522652026
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
noncomputable def negativeCeiling : ℝ := 540165797 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1033631575770507944373780480, coefficient := (-1033631575770507944373780480) }, { argument := 53834977904713955436134400, coefficient := (-53834977904713955436134400) }, { argument := 1658117319465189827432939520, coefficient := (-1658117319465189827432939520) }, { argument := 936728615542022824588738560, coefficient := (-936728615542022824588738560) }, { argument := 151235637052915281958010880, coefficient := (-151235637052915281958010880) }, { argument := 9646930320086893113636814848, coefficient := (-9646930320086893113636814848) }, { argument := 349996538295968878194193334272, coefficient := (-349996538295968878194193334272) }, { argument := 349995235950982956851497271296, coefficient := (-349995235950982956851497271296) }, { argument := 9648234595063413168194715648, coefficient := (-9648234595063413168194715648) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1416143260882949206683156480, coefficient := (-1416143260882949206683156480) }, { argument := 1618449441009084807637893120, coefficient := (-1618449441009084807637893120) }, { argument := 1901678093185674648974524416, coefficient := (-1901678093185674648974524416) }, { argument := 22455985994001051705975767040, coefficient := (-22455985994001051705975767040) }, { argument := 50495622559483445998302265344, coefficient := (-50495622559483445998302265344) }, { argument := 1416143260882949206683156480, coefficient := (-1416143260882949206683156480) }, { argument := 22455985994001051705975767040, coefficient := (-22455985994001051705975767040) }, { argument := 1618449441009084807637893120, coefficient := (-1618449441009084807637893120) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 50495622559483445998302265344, coefficient := (-50495622559483445998302265344) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1901678093185674648974524416, coefficient := (-1901678093185674648974524416) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 805257932658931901839441920, coefficient := (-805257932658931901839441920) }, { argument := 920294780181636459245076480, coefficient := (-920294780181636459245076480) }, { argument := 1081346366713422839612964864, coefficient := (-1081346366713422839612964864) }, { argument := 12769090075020205872025436160, coefficient := (-12769090075020205872025436160) }, { argument := 28713197141667057528446386176, coefficient := (-28713197141667057528446386176) }, { argument := 805257932658931901839441920, coefficient := (-805257932658931901839441920) }, { argument := 12769090075020205872025436160, coefficient := (-12769090075020205872025436160) }, { argument := 920294780181636459245076480, coefficient := (-920294780181636459245076480) }, { argument := 897287410677095547763949568, coefficient := (-897287410677095547763949568) }, { argument := 897287410677095547763949568, coefficient := (-897287410677095547763949568) }, { argument := 897287410677095547763949568, coefficient := (-897287410677095547763949568) }, { argument := 28713197141667057528446386176, coefficient := (-28713197141667057528446386176) }, { argument := 897287410677095547763949568, coefficient := (-897287410677095547763949568) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 1081346366713422839612964864, coefficient := (-1081346366713422839612964864) }, { argument := 152648748729760297552707584, coefficient := (-152648748729760297552707584) }, { argument := 14275749041820827989835776000, coefficient := (-14275749041820827989835776000) }, { argument := 1935636630563990267706212352, coefficient := (-1935636630563990267706212352) }, { argument := 122315339850071209925284986880, coefficient := (-122315339850071209925284986880) }, { argument := 1986241509794421385816178688, coefficient := (-1986241509794421385816178688) }, { argument := 63256099038038897637457920, coefficient := (-63256099038038897637457920) }, { argument := 1935636630563990267706212352, coefficient := (-1935636630563990267706212352) }, { argument := 1100656123261876818891767808, coefficient := (-1100656123261876818891767808) }, { argument := 1986241509794421385816178688, coefficient := (-1986241509794421385816178688) }, { argument := 31008139748446667621881872384, coefficient := (-31008139748446667621881872384) }, { argument := 1214517101530346834639192064, coefficient := (-1214517101530346834639192064) }, { argument := 14275749041820827989835776000, coefficient := (-14275749041820827989835776000) }, { argument := 1935636630563990267706212352, coefficient := (-1935636630563990267706212352) }, { argument := 63256099038038897637457920, coefficient := (-63256099038038897637457920) }, { argument := 1214517101530346834639192064, coefficient := (-1214517101530346834639192064) }, { argument := 63256099038038897637457920, coefficient := (-63256099038038897637457920) }, { argument := 1948287850371598047233703936, coefficient := (-1948287850371598047233703936) }, { argument := 1100656123261876818891767808, coefficient := (-1100656123261876818891767808) }, { argument := 152639992290932808549924864, coefficient := (-152639992290932808549924864) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 1453166614108647225158533120, coefficient := (-1453166614108647225158533120) }, { argument := 1660761844695596828752609280, coefficient := (-1660761844695596828752609280) }, { argument := 1951395167517326273784315904, coefficient := (-1951395167517326273784315904) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
