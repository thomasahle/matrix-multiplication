import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-88993762435677110724763305639936)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    35, 38762793, 187729623, 38762793, 45047275, 3771769365,
    1885885365, 22522955, 64604655, 312882705, 64604655, 19305975,
    1616472585, 808236585, 9652695, 2188025, 229410475, 2472815625,
    114705325, 2188025, 47, 47, 47, 47,
    994911687, 4818393657, 994911687, 45047275, 3771769365, 1885885365,
    22522955, 1124120997, 5444159067, 1124120997, 508390675, 42567111405,
    21283563405, 254187635, 70629447, 7405370133, 79822488375, 3702687891,
    70629447, 19305975, 1616472585, 808236585, 9652695, 47173819,
    4946089841, 53313904875, 2473046807, 47173819, 569765685, 9970189215,
    9970194105, 569760795, 86590261, 181656087, 1055854159, 292607709,
    9064675, 292607709, 195434393, 5434553
  ]
def negativeCoefficients : Array ℕ := #[
    169249614746048084458864640, 1430094644106360182827646976, 13852001242139913345482883072, 1430094644106360182827646976, 207743888285753610443161600, 17394216045303247173278760960,
    17394222340254662326663249920, 207737593334338457058672640, 74484096047206259522273280, 721458398028120486743900160, 74484096047206259522273280, 178066189959217380379852800,
    14909328038831354719953223680, 14909333434503996279997071360, 178060794286575820336005120, 10090484300469585418649600, 1057969080038285812065894400, 11403849243961282736947200000,
    1057969887083339036858777600, 10090484300469585418649600, 227278054087550284844761088, 227278054087550284844761088, 227278054087550284844761088, 227278054087550284844761088,
    2294110158253952793286017024, 22220918659266110991712124928, 2294110158253952793286017024, 207743888285753610443161600, 17394216045303247173278760960, 17394222340254662326663249920,
    207737593334338457058672640, 1296023271221388915687555072, 12553376125689296469343862784, 1296023271221388915687555072, 2344538167796362175001395200, 196306152511279503812717445120,
    196306223554302617686628106240, 2344467124773248301090734080, 325720833219158217314009088, 34151241903635866013487071232, 368116253595070206748655616000, 34151267955050184109801340928,
    325720833219158217314009088, 178066189959217380379852800, 14909328038831354719953223680, 14909333434503996279997071360, 178060794286575820336005120, 217550841518124261626085376,
    22809813365625442108140683264, 245866989699805255808581632000, 22809830765516789634675245056, 217550841518124261626085376, 1313790221647101645941637120, 45979382203891034141082255360,
    45979404755035664251009105920, 1313778946074786590978211840, 99831773996419582038900736, 209435209145032295067942912, 1217316965639677039486173184, 337353720119842439360937984,
    10450858739772070612172800, 337353720119842439360937984, 225320514429485842398445568, 100249808346010464863387648
  ]
def negativeScales : Array ℕ := #[
    5, 25, 27, 25, 25, 31,
    30, 24, 25, 28, 25, 24,
    30, 29, 23, 21, 27, 31,
    26, 21, 5, 5, 5, 5,
    29, 32, 29, 25, 31, 30,
    24, 30, 32, 30, 28, 35,
    34, 27, 26, 32, 36, 31,
    26, 24, 30, 29, 23, 25,
    32, 35, 31, 25, 29, 33,
    33, 29, 26, 27, 29, 28,
    23, 28, 27, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    5129283016944967, 25208169190126491, 27484081078863778, 25208169190126491, 25424936501373755, 31812594316054369,
    30812594838164344, 24424892784887741, 25945134793892351, 28221046673029826, 25945134793892351, 24202544080037289,
    30590201893888873, 29590202415998839, 23202500363551276, 21061197791535984, 27773356026523965, 31203507529292607,
    26773357127047112, 21061197791535984, 5554588851679165, 5554588851679165, 5554588851679165, 5554588851679165,
    29889993233746516, 32165905118837365, 29889993233746516, 25424936501373755, 31812594316054369, 30812594838164344,
    24424892784887741, 30066150185254063, 32342062073991193, 30066150185254063, 28921362333867493, 35309020141340518,
    34309020663450484, 27921318617376613, 26073766465039040, 32785924700139021, 36216076202795663, 31785925800662170,
    26073766465039040, 24202544080037289, 30590201893888873, 29590202415998839, 23202500363551276, 25491483064513968,
    32203641299130209, 35633792802284417, 31203642399653347, 25491483064513968, 29085793494886519, 33214973738444420,
    33214974446031495, 29085781112938624, 26367701435155295, 27436634468026464, 29975763444629539, 28124392538109008,
    23111823864605952, 28124392538109008, 27542109137584778, 22373729945661599
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
noncomputable def negativeCeiling : ℝ := 295022787 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 1430094644106360182827646976, coefficient := (-1430094644106360182827646976) }, { argument := 13852001242139913345482883072, coefficient := (-13852001242139913345482883072) }, { argument := 1430094644106360182827646976, coefficient := (-1430094644106360182827646976) }, { argument := 207743888285753610443161600, coefficient := (-207743888285753610443161600) }, { argument := 17394216045303247173278760960, coefficient := (-17394216045303247173278760960) }, { argument := 17394222340254662326663249920, coefficient := (-17394222340254662326663249920) }, { argument := 207737593334338457058672640, coefficient := (-207737593334338457058672640) }, { argument := 74484096047206259522273280, coefficient := (-74484096047206259522273280) }, { argument := 721458398028120486743900160, coefficient := (-721458398028120486743900160) }, { argument := 74484096047206259522273280, coefficient := (-74484096047206259522273280) }, { argument := 178066189959217380379852800, coefficient := (-178066189959217380379852800) }, { argument := 14909328038831354719953223680, coefficient := (-14909328038831354719953223680) }, { argument := 14909333434503996279997071360, coefficient := (-14909333434503996279997071360) }, { argument := 178060794286575820336005120, coefficient := (-178060794286575820336005120) }, { argument := 10090484300469585418649600, coefficient := (-10090484300469585418649600) }, { argument := 1057969080038285812065894400, coefficient := (-1057969080038285812065894400) }, { argument := 11403849243961282736947200000, coefficient := (-11403849243961282736947200000) }, { argument := 1057969887083339036858777600, coefficient := (-1057969887083339036858777600) }, { argument := 10090484300469585418649600, coefficient := (-10090484300469585418649600) }, { argument := 227278054087550284844761088, coefficient := (-227278054087550284844761088) }, { argument := 227278054087550284844761088, coefficient := (-227278054087550284844761088) }, { argument := 227278054087550284844761088, coefficient := (-227278054087550284844761088) }, { argument := 227278054087550284844761088, coefficient := (-227278054087550284844761088) }, { argument := 2294110158253952793286017024, coefficient := (-2294110158253952793286017024) }, { argument := 22220918659266110991712124928, coefficient := (-22220918659266110991712124928) }, { argument := 2294110158253952793286017024, coefficient := (-2294110158253952793286017024) }, { argument := 207743888285753610443161600, coefficient := (-207743888285753610443161600) }, { argument := 17394216045303247173278760960, coefficient := (-17394216045303247173278760960) }, { argument := 17394222340254662326663249920, coefficient := (-17394222340254662326663249920) }, { argument := 207737593334338457058672640, coefficient := (-207737593334338457058672640) }, { argument := 1296023271221388915687555072, coefficient := (-1296023271221388915687555072) }, { argument := 12553376125689296469343862784, coefficient := (-12553376125689296469343862784) }, { argument := 1296023271221388915687555072, coefficient := (-1296023271221388915687555072) }, { argument := 2344538167796362175001395200, coefficient := (-2344538167796362175001395200) }, { argument := 196306152511279503812717445120, coefficient := (-196306152511279503812717445120) }, { argument := 196306223554302617686628106240, coefficient := (-196306223554302617686628106240) }, { argument := 2344467124773248301090734080, coefficient := (-2344467124773248301090734080) }, { argument := 325720833219158217314009088, coefficient := (-325720833219158217314009088) }, { argument := 34151241903635866013487071232, coefficient := (-34151241903635866013487071232) }, { argument := 368116253595070206748655616000, coefficient := (-368116253595070206748655616000) }, { argument := 34151267955050184109801340928, coefficient := (-34151267955050184109801340928) }, { argument := 325720833219158217314009088, coefficient := (-325720833219158217314009088) }, { argument := 178066189959217380379852800, coefficient := (-178066189959217380379852800) }, { argument := 14909328038831354719953223680, coefficient := (-14909328038831354719953223680) }, { argument := 14909333434503996279997071360, coefficient := (-14909333434503996279997071360) }, { argument := 178060794286575820336005120, coefficient := (-178060794286575820336005120) }, { argument := 217550841518124261626085376, coefficient := (-217550841518124261626085376) }, { argument := 22809813365625442108140683264, coefficient := (-22809813365625442108140683264) }, { argument := 245866989699805255808581632000, coefficient := (-245866989699805255808581632000) }, { argument := 22809830765516789634675245056, coefficient := (-22809830765516789634675245056) }, { argument := 217550841518124261626085376, coefficient := (-217550841518124261626085376) }, { argument := 1313790221647101645941637120, coefficient := (-1313790221647101645941637120) }, { argument := 45979382203891034141082255360, coefficient := (-45979382203891034141082255360) }, { argument := 45979404755035664251009105920, coefficient := (-45979404755035664251009105920) }, { argument := 1313778946074786590978211840, coefficient := (-1313778946074786590978211840) }, { argument := 99831773996419582038900736, coefficient := (-99831773996419582038900736) }, { argument := 209435209145032295067942912, coefficient := (-209435209145032295067942912) }, { argument := 1217316965639677039486173184, coefficient := (-1217316965639677039486173184) }, { argument := 337353720119842439360937984, coefficient := (-337353720119842439360937984) }, { argument := 10450858739772070612172800, coefficient := (-10450858739772070612172800) }, { argument := 337353720119842439360937984, coefficient := (-337353720119842439360937984) }, { argument := 225320514429485842398445568, coefficient := (-225320514429485842398445568) }, { argument := 100249808346010464863387648, coefficient := (-100249808346010464863387648) }] }

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


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 1436870066269368451084083487834112
def positiveArguments : Array ℕ := #[
    193, 1
  ]
def positiveCoefficients : Array ℕ := #[
    15291035365253017155553982414848, 158456325028528675187087900672
  ]
def positiveScales : Array ℕ := #[
    7, 0
  ]
def negativeArguments : Array ℕ := #[
    181656087, 1087761, 90093185, 3818102301, 22522955, 19948903,
    933737363, 254187635, 1909051833, 933737363, 22522955, 22522955,
    9652695, 22522955, 254187635, 9652695, 22522955, 19948903,
    23810431, 406425247, 1098279135, 5179347975, 1126992315, 35891475,
    1098279135, 624511665, 1126992315, 17594001045, 21534885, 203212669,
    1098279135, 35891475, 21534885, 35891475, 552728715, 624511665,
    23810431, 39899015, 3340710009, 1670355609, 19948903, 43848021,
    4597385919, 49555225125, 2298694713, 43848021, 623363275, 10908080225,
    10908085575, 623357925, 262563, 27529257, 296737875, 13764639,
    262563, 569765685, 9970189215, 9970194105, 569760795, 386995,
    10585297, 3095959
  ]
def negativeCoefficients : Array ℕ := #[
    209435209145032295067942912, 10032824390181187787685888, 415481481620092067501834240, 17607888998447138157681967104, 207737593334338457058672640, 183996154096128347680538624,
    8612207083660717176918114304, 2344467124773248301090734080, 17607895293398553311066456064, 8612207083660717176918114304, 207737593334338457058672640, 207737593334338457058672640,
    178060794286575820336005120, 207737593334338457058672640, 2344467124773248301090734080, 178060794286575820336005120, 415475186668676914117345280, 183996154096128347680538624,
    109806231735430048198426624, 3748611258251595360896024576, 2532459265605012823757291520, 11942763320438852112560947200, 2598667350980307276665978880, 82760106719118066135859200,
    2532459265605012823757291520, 1440025856912654350763950080, 2598667350980307276665978880, 40569004313711676019798179840, 1588994049007066869808496640, 3748612097578450714680623104,
    2532459265605012823757291520, 82760106719118066135859200, 1588994049007066869808496640, 82760106719118066135859200, 2549011286948836436984463360, 1440025856912654350763950080,
    109806231735430048198426624, 184001729624524626392514560, 15406305640125733210618331136, 15406311215654129489330307072, 183996154096128347680538624, 202213305381410491789737984,
    21201700363967247673800523776, 228533138848984106048421888000, 21201716537150114298649903104, 202213305381410491789737984, 1437377849859303436766412800, 50304641061516775594026598400,
    50304665734036974180551884800, 1437365513599204143503769600, 9686864928450802001903616, 1015650316836754379583258624, 10947695274202831427469312000, 1015651091600005475384426496,
    9686864928450802001903616, 1313790221647101645941637120, 45979382203891034141082255360, 45979404755035664251009105920, 1313778946074786590978211840, 14620257736305106795794268160,
    49987651764020606871600627712, 14620253013938623926149054464
  ]
def negativeScales : Array ℕ := #[
    27, 20, 26, 31, 24, 24,
    29, 27, 30, 29, 24, 24,
    23, 24, 27, 23, 24, 24,
    24, 28, 30, 32, 30, 25,
    30, 29, 30, 34, 24, 27,
    30, 25, 24, 25, 29, 29,
    24, 25, 31, 30, 24, 25,
    32, 35, 31, 25, 29, 33,
    33, 29, 18, 24, 28, 23,
    18, 29, 33, 33, 29, 18,
    23, 21
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7592457037267794, 0
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    27436634468026464, 20052930175552383, 26424914643296335, 31830208613532382, 24424892784887741, 24249806078329632,
    29798441572635311, 27921318617376613, 30830209129306520, 29798441572635311, 24424892784887741, 24424892784887741,
    23202500363551276, 24424892784887741, 27921318617376613, 23202500363551276, 24424892784887741, 24249806078329632,
    24505090399727072, 28598414783730037, 30032597625543036, 32270123343318565, 30069830531742012, 25097137877737747,
    30032597625543036, 29218153278699113, 30069830531742012, 34034364551717224, 24360172283571542, 27598415106754345,
    30032597625543036, 25097137877737747, 24360172283571542, 25097137877737747, 29041996323545286, 29218153278699113,
    24505090399727072, 25249849794815646, 31637507608678382, 30637508130788348, 24249806078329632, 25386008394956471,
    32098166629572912, 35528318132713771, 31098167730096050, 25386008394956471, 29215497921222795, 33344678164780696,
    33344678872367771, 29215485539274900, 18002304102482415, 24714462337200208, 28144613840239039, 23714463437723348,
    18002304102482415, 29085793494886519, 33214973738444420, 33214974446031495, 29085781112938624, 18561955401217177,
    23335558412953920, 21561954935224311
  ]

abbrev PositiveTerm := Fin 2
abbrev NegativeTerm := Fin 62
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
noncomputable def positiveFloor : ℝ := 87341321 / 62500000000
noncomputable def negativeCeiling : ℝ := 56667969 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 209435209145032295067942912, coefficient := (-209435209145032295067942912) }, { argument := 10032824390181187787685888, coefficient := (-10032824390181187787685888) }, { argument := 415481481620092067501834240, coefficient := (-415481481620092067501834240) }, { argument := 17607888998447138157681967104, coefficient := (-17607888998447138157681967104) }, { argument := 207737593334338457058672640, coefficient := (-207737593334338457058672640) }, { argument := 183996154096128347680538624, coefficient := (-183996154096128347680538624) }, { argument := 8612207083660717176918114304, coefficient := (-8612207083660717176918114304) }, { argument := 2344467124773248301090734080, coefficient := (-2344467124773248301090734080) }, { argument := 17607895293398553311066456064, coefficient := (-17607895293398553311066456064) }, { argument := 8612207083660717176918114304, coefficient := (-8612207083660717176918114304) }, { argument := 207737593334338457058672640, coefficient := (-207737593334338457058672640) }, { argument := 207737593334338457058672640, coefficient := (-207737593334338457058672640) }, { argument := 178060794286575820336005120, coefficient := (-178060794286575820336005120) }, { argument := 207737593334338457058672640, coefficient := (-207737593334338457058672640) }, { argument := 2344467124773248301090734080, coefficient := (-2344467124773248301090734080) }, { argument := 178060794286575820336005120, coefficient := (-178060794286575820336005120) }, { argument := 415475186668676914117345280, coefficient := (-415475186668676914117345280) }, { argument := 183996154096128347680538624, coefficient := (-183996154096128347680538624) }, { argument := 109806231735430048198426624, coefficient := (-109806231735430048198426624) }, { argument := 3748611258251595360896024576, coefficient := (-3748611258251595360896024576) }, { argument := 2532459265605012823757291520, coefficient := (-2532459265605012823757291520) }, { argument := 11942763320438852112560947200, coefficient := (-11942763320438852112560947200) }, { argument := 2598667350980307276665978880, coefficient := (-2598667350980307276665978880) }, { argument := 82760106719118066135859200, coefficient := (-82760106719118066135859200) }, { argument := 2532459265605012823757291520, coefficient := (-2532459265605012823757291520) }, { argument := 1440025856912654350763950080, coefficient := (-1440025856912654350763950080) }, { argument := 2598667350980307276665978880, coefficient := (-2598667350980307276665978880) }, { argument := 40569004313711676019798179840, coefficient := (-40569004313711676019798179840) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 3748612097578450714680623104, coefficient := (-3748612097578450714680623104) }, { argument := 2532459265605012823757291520, coefficient := (-2532459265605012823757291520) }, { argument := 82760106719118066135859200, coefficient := (-82760106719118066135859200) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 82760106719118066135859200, coefficient := (-82760106719118066135859200) }, { argument := 2549011286948836436984463360, coefficient := (-2549011286948836436984463360) }, { argument := 1440025856912654350763950080, coefficient := (-1440025856912654350763950080) }, { argument := 109806231735430048198426624, coefficient := (-109806231735430048198426624) }, { argument := 184001729624524626392514560, coefficient := (-184001729624524626392514560) }, { argument := 15406305640125733210618331136, coefficient := (-15406305640125733210618331136) }, { argument := 15406311215654129489330307072, coefficient := (-15406311215654129489330307072) }, { argument := 183996154096128347680538624, coefficient := (-183996154096128347680538624) }, { argument := 202213305381410491789737984, coefficient := (-202213305381410491789737984) }, { argument := 21201700363967247673800523776, coefficient := (-21201700363967247673800523776) }, { argument := 228533138848984106048421888000, coefficient := (-228533138848984106048421888000) }, { argument := 21201716537150114298649903104, coefficient := (-21201716537150114298649903104) }, { argument := 202213305381410491789737984, coefficient := (-202213305381410491789737984) }, { argument := 1437377849859303436766412800, coefficient := (-1437377849859303436766412800) }, { argument := 50304641061516775594026598400, coefficient := (-50304641061516775594026598400) }, { argument := 50304665734036974180551884800, coefficient := (-50304665734036974180551884800) }, { argument := 1437365513599204143503769600, coefficient := (-1437365513599204143503769600) }, { argument := 9686864928450802001903616, coefficient := (-9686864928450802001903616) }, { argument := 1015650316836754379583258624, coefficient := (-1015650316836754379583258624) }, { argument := 10947695274202831427469312000, coefficient := (-10947695274202831427469312000) }, { argument := 1015651091600005475384426496, coefficient := (-1015651091600005475384426496) }, { argument := 9686864928450802001903616, coefficient := (-9686864928450802001903616) }, { argument := 1313790221647101645941637120, coefficient := (-1313790221647101645941637120) }, { argument := 45979382203891034141082255360, coefficient := (-45979382203891034141082255360) }, { argument := 45979404755035664251009105920, coefficient := (-45979404755035664251009105920) }, { argument := 1313778946074786590978211840, coefficient := (-1313778946074786590978211840) }, { argument := 14620257736305106795794268160, coefficient := (-14620257736305106795794268160) }, { argument := 49987651764020606871600627712, coefficient := (-49987651764020606871600627712) }, { argument := 14620253013938623926149054464, coefficient := (-14620253013938623926149054464) }, { argument := 15291035365253017155553982414848, coefficient := 15291035365253017155553982414848 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0
