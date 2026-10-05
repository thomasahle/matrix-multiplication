import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1487343635407638270585400419418112)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    17833875, 3127894125, 781973625, 4458375, 134943, 3269103,
    2476857, 1379901, 134943, 1379901, 2755449, 134943,
    3269103, 134943, 14570275875, 2555489500125, 638872451625, 3642492375,
    128153115, 82561711185, 878078517993, 41280980013, 128153115, 933306125,
    163693125875, 40923286375, 233321625, 231791715, 149330124585, 1588188672513,
    74665287333, 231791715, 178204527, 78855, 27214476365, 889935,
    78855, 6803621585, 78855, 78855, 3269103, 20277,
    889935, 3269103, 712828083, 78855, 20277, 78855,
    2216426318707, 183170937, 73667399598181, 1209615045, 59789049, 603866991,
    1228378059, 277878465157, 183170937, 59789049, 7979318938353, 393199555769615,
    288487927, 23390913, 5013452353, 9067877273
  ]
def negativeCoefficients : Array ℕ := #[
    657953855935053859651584000, 115398924827069346912141312000, 115398938662127402194305024000, 657940020876998577487872000, 637250300297878534071779328, 15437902436248605777029234688,
    11696626479661060835059433472, 13032796464156612600048648192, 637250300297878534071779328, 13032796464156612600048648192, 13012240002856681034433429504, 637250300297878534071779328,
    15437902436248605777029234688, 637250300297878534071779328, 16798384384341843854229504000, 2946278799491114263350607872000, 2946279152717440237273350144000, 16798031158015869931487232000,
    1182003857326834322421841920, 380748689129304588024010506240, 4049422424509759659226454556672, 380749836705865099513643925504, 1182003857326834322421841920, 1076028701893785999638528000,
    188725324977602994429231104000, 188725347603687522338603008000, 1076006075809258090266624000, 2137901222505611690476830720, 688663647678664441480442019840, 7324227495652955651135873482752,
    688665723310919301297617240064, 2137901222505611690476830720, 13149173209381855124445462528, 372382209006685873325998080, 502018480605172410328379555840, 4202599215932597713250549760,
    372382209006685873325998080, 502018664611444545581156925440, 372382209006685873325998080, 372382209006685873325998080, 15437902436248605777029234688, 383021700692591183992455168,
    4202599215932597713250549760, 15437902436248605777029234688, 13149357215653990377222832128, 372382209006685873325998080, 383021700692591183992455168, 372382209006685873325998080,
    1247737092877875675958083584, 13515629586322302541410336768, 41471059172465172295001833472, 11156729581411831297458831360, 551456642656739996668526592, 11139379837538069142313107456,
    11329787840066545971911196672, 1251453352135350556265807872, 13515629586322302541410336768, 551456642656739996668526592, 35935657797436912543715033088, 1770813372846282674548024279040,
    21286651830896014983197360128, 27615115888729965383607386112, 369927489926111827951240609792, 669091245387353119606987292672
  ]
def negativeScales : Array ℕ := #[
    24, 31, 29, 22, 17, 21,
    21, 20, 17, 20, 21, 17,
    21, 17, 33, 41, 39, 31,
    26, 36, 39, 35, 26, 29,
    37, 35, 27, 27, 37, 40,
    36, 27, 27, 16, 34, 19,
    16, 32, 16, 16, 21, 14,
    19, 21, 29, 16, 14, 16,
    41, 27, 46, 30, 25, 29,
    30, 38, 27, 25, 42, 48,
    28, 24, 32, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    24088116874515161, 31542544534176532, 29542544707139742, 22088086538072384, 17041990615174776, 21640463402318857,
    21240079147094483, 20396133334927314, 17041990615174776, 20396133334927314, 21393855994216248, 17041990615174776,
    21640463402318857, 17041990615174776, 33762309142954450, 41216736802321156, 39216736975284366, 31762278806511481,
    26933293313382749, 36264753821433845, 39675558995468881, 35264758169710189, 26933293313382749, 29797775123302974,
    37252202782345944, 35252202955309154, 27797744786859814, 27788253760195689, 37119714275579116, 40530519449574589,
    36119718623855460, 27788253760195689, 27408958745776328, 16266914615180395, 34663655226271635, 19763340441600069,
    16266914615180395, 32663655755066686, 16266914615180395, 16266914615180395, 21640463402318857, 14307556599677741,
    19763340441600069, 21640463402318857, 29408978934352041, 16266914615180395, 14307556599677741, 16266914615180395,
    41011372542025484, 27448615374039507, 46066091551048048, 30171900842781484, 25833377929153047, 29169655572628816,
    30194107502563297, 38015663077597686, 27448615374039507, 25833377929153047, 42859402753558363, 48482255020169529,
    28103935703544418, 24479444838636759, 32223157265243416, 33078117719388687
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
noncomputable def negativeCeiling : ℝ := 2882813707 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 657953855935053859651584000, coefficient := (-657953855935053859651584000) }, { argument := 115398924827069346912141312000, coefficient := (-115398924827069346912141312000) }, { argument := 115398938662127402194305024000, coefficient := (-115398938662127402194305024000) }, { argument := 657940020876998577487872000, coefficient := (-657940020876998577487872000) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15437902436248605777029234688, coefficient := (-15437902436248605777029234688) }, { argument := 11696626479661060835059433472, coefficient := (-11696626479661060835059433472) }, { argument := 13032796464156612600048648192, coefficient := (-13032796464156612600048648192) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 13032796464156612600048648192, coefficient := (-13032796464156612600048648192) }, { argument := 13012240002856681034433429504, coefficient := (-13012240002856681034433429504) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15437902436248605777029234688, coefficient := (-15437902436248605777029234688) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 16798384384341843854229504000, coefficient := (-16798384384341843854229504000) }, { argument := 2946278799491114263350607872000, coefficient := (-2946278799491114263350607872000) }, { argument := 2946279152717440237273350144000, coefficient := (-2946279152717440237273350144000) }, { argument := 16798031158015869931487232000, coefficient := (-16798031158015869931487232000) }, { argument := 1182003857326834322421841920, coefficient := (-1182003857326834322421841920) }, { argument := 380748689129304588024010506240, coefficient := (-380748689129304588024010506240) }, { argument := 4049422424509759659226454556672, coefficient := (-4049422424509759659226454556672) }, { argument := 380749836705865099513643925504, coefficient := (-380749836705865099513643925504) }, { argument := 1182003857326834322421841920, coefficient := (-1182003857326834322421841920) }, { argument := 1076028701893785999638528000, coefficient := (-1076028701893785999638528000) }, { argument := 188725324977602994429231104000, coefficient := (-188725324977602994429231104000) }, { argument := 188725347603687522338603008000, coefficient := (-188725347603687522338603008000) }, { argument := 1076006075809258090266624000, coefficient := (-1076006075809258090266624000) }, { argument := 2137901222505611690476830720, coefficient := (-2137901222505611690476830720) }, { argument := 688663647678664441480442019840, coefficient := (-688663647678664441480442019840) }, { argument := 7324227495652955651135873482752, coefficient := (-7324227495652955651135873482752) }, { argument := 688665723310919301297617240064, coefficient := (-688665723310919301297617240064) }, { argument := 2137901222505611690476830720, coefficient := (-2137901222505611690476830720) }, { argument := 13149173209381855124445462528, coefficient := (-13149173209381855124445462528) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 502018480605172410328379555840, coefficient := (-502018480605172410328379555840) }, { argument := 4202599215932597713250549760, coefficient := (-4202599215932597713250549760) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 502018664611444545581156925440, coefficient := (-502018664611444545581156925440) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 15437902436248605777029234688, coefficient := (-15437902436248605777029234688) }, { argument := 383021700692591183992455168, coefficient := (-383021700692591183992455168) }, { argument := 4202599215932597713250549760, coefficient := (-4202599215932597713250549760) }, { argument := 15437902436248605777029234688, coefficient := (-15437902436248605777029234688) }, { argument := 13149357215653990377222832128, coefficient := (-13149357215653990377222832128) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 383021700692591183992455168, coefficient := (-383021700692591183992455168) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 1247737092877875675958083584, coefficient := (-1247737092877875675958083584) }, { argument := 13515629586322302541410336768, coefficient := (-13515629586322302541410336768) }, { argument := 41471059172465172295001833472, coefficient := (-41471059172465172295001833472) }, { argument := 11156729581411831297458831360, coefficient := (-11156729581411831297458831360) }, { argument := 551456642656739996668526592, coefficient := (-551456642656739996668526592) }, { argument := 11139379837538069142313107456, coefficient := (-11139379837538069142313107456) }, { argument := 11329787840066545971911196672, coefficient := (-11329787840066545971911196672) }, { argument := 1251453352135350556265807872, coefficient := (-1251453352135350556265807872) }, { argument := 13515629586322302541410336768, coefficient := (-13515629586322302541410336768) }, { argument := 551456642656739996668526592, coefficient := (-551456642656739996668526592) }, { argument := 35935657797436912543715033088, coefficient := (-35935657797436912543715033088) }, { argument := 1770813372846282674548024279040, coefficient := (-1770813372846282674548024279040) }, { argument := 21286651830896014983197360128, coefficient := (-21286651830896014983197360128) }, { argument := 27615115888729965383607386112, coefficient := (-27615115888729965383607386112) }, { argument := 369927489926111827951240609792, coefficient := (-369927489926111827951240609792) }, { argument := 669091245387353119606987292672, coefficient := (-669091245387353119606987292672) }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2053377297594278002765086945443840)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    393199558553615, 5013452353, 148142449, 148142449, 288487927, 288487927,
    9067877273, 288487927, 7979316154353, 23390913, 15348006473751, 388013067306963,
    20391786877, 7509532144550045, 794485203, 1324142005, 40518745353, 1324142005,
    794485203, 649094410851, 41578058957, 388013081177043, 40518745353, 1324142005,
    41578058957, 1324142005, 40518745353, 1324142005, 15348006473751, 909527625,
    159522600375, 39880654875, 227377125, 128153115, 82561711185, 878078517993,
    41280980013, 128153115, 149660481310687, 59745, 1480087125357235, 674265,
    59745, 2960173930162875, 59745, 59745, 2476857, 15363,
    674265, 2476857, 149660964720607, 59745, 15363, 59745,
    3786795, 2439615105, 25946332569, 1219811229, 3786795, 1176836739,
    33285, 179618202825, 375645, 33285
  ]
def negativeCoefficients : Array ℕ := #[
    1770813385384304037147485143040, 369927489926111827951240609792, 21861966745244555928689180672, 21861966745244555928689180672, 21286651830896014983197360128, 21286651830896014983197360128,
    669091245387353119606987292672, 21286651830896014983197360128, 35935645259415549944254169088, 27615115888729965383607386112, 17280319059016240974343962624, 1747455505338521750687761563648,
    188081036862823977676351471616, 16909963083961172183130214236160, 117245321680721440629413904384, 6106527170870908366115307520, 186859731428649796003128410112, 195408869467869067715689840640,
    117245321680721440629413904384, 2993419619160919281069723746304, 191744953165346522696020656128, 1747455567803808870286730723328, 186859731428649796003128410112, 6106527170870908366115307520,
    191744953165346522696020656128, 6106527170870908366115307520, 186859731428649796003128410112, 195408869467869067715689840640, 17280319059016240974343962624, 1048613957896492088819712000,
    183917036443141771641225216000, 183917058492765547247173632000, 1048591908272716482871296000, 1182003857326834322421841920, 380748689129304588024010506240, 4049422424509759659226454556672,
    380749836705865099513643925504, 1182003857326834322421841920, 42125680491431190874839580672, 282137785519046953292267520, 1666429956558678036836924784640, 3184126436572101330012733440,
    282137785519046953292267520, 1666429776104172562459656192000, 282137785519046953292267520, 282137785519046953292267520, 11696626479661060835059433472, 290198865105305437672046592,
    3184126436572101330012733440, 11696626479661060835059433472, 42125816559227164574919688192, 282137785519046953292267520, 290198865105305437672046592, 282137785519046953292267520,
    69854038224602961511710720, 22501477740145527752585379840, 239312678275848937870303690752, 22501545559600114745751896064, 69854038224602961511710720, 10854403070435962178462810112,
    314367936764632281875742720, 414171377311553624037811814400, 3547866714915135752597667840, 314367936764632281875742720
  ]
def negativeScales : Array ℕ := #[
    48, 32, 27, 27, 28, 28,
    33, 28, 42, 24, 43, 48,
    34, 52, 29, 30, 35, 30,
    29, 39, 35, 48, 35, 30,
    35, 30, 35, 30, 43, 29,
    37, 35, 27, 26, 36, 39,
    35, 26, 47, 15, 50, 19,
    15, 51, 15, 15, 21, 13,
    19, 21, 47, 15, 13, 15,
    21, 31, 34, 30, 21, 30,
    15, 37, 18, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    48482255030384350, 32223157265243416, 27142409851359054, 27142409851359054, 28103935703544418, 28103935703544418,
    33078117719388687, 28103935703544418, 42859402250199131, 24479444838636759, 43803116512802688, 48463098568004375,
    34247269149222507, 52737644451891942, 29565445109250871, 30302410703414968, 35237870451220257, 30302410703414968,
    29565445109250871, 39239637377394445, 35275103357419232, 48463098619575564, 35237870451220257, 30302410703414968,
    35275103357419232, 30302410703414968, 35237870451220257, 30302410703414968, 43803116512802688, 29760542216769316,
    37214969876146969, 35214970049110178, 27760511880326354, 26933293313382749, 36264753821433845, 39675558995468881,
    35264758169710189, 26933293313382749, 47088686648391293, 15866530362339582, 50394603525935759, 19362956186092205,
    15866530362339582, 51394603369709070, 15866530362339582, 15866530362339582, 21240079147094483, 13907172349434197,
    19362956186092205, 21240079147094483, 47088691308352038, 15866530362339582, 13907172349434197, 15866530362339582,
    21852545893476809, 31184006407549483, 34594811581549123, 30184010755825827, 21852545893476809, 30132267045074512,
    15022584547805530, 37386142606505074, 18519010373925535, 15022584547805530
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
noncomputable def negativeCeiling : ℝ := 21250664911 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1770813385384304037147485143040, coefficient := (-1770813385384304037147485143040) }, { argument := 369927489926111827951240609792, coefficient := (-369927489926111827951240609792) }, { argument := 21861966745244555928689180672, coefficient := (-21861966745244555928689180672) }, { argument := 21861966745244555928689180672, coefficient := (-21861966745244555928689180672) }, { argument := 21286651830896014983197360128, coefficient := (-21286651830896014983197360128) }, { argument := 21286651830896014983197360128, coefficient := (-21286651830896014983197360128) }, { argument := 669091245387353119606987292672, coefficient := (-669091245387353119606987292672) }, { argument := 21286651830896014983197360128, coefficient := (-21286651830896014983197360128) }, { argument := 35935645259415549944254169088, coefficient := (-35935645259415549944254169088) }, { argument := 27615115888729965383607386112, coefficient := (-27615115888729965383607386112) }, { argument := 17280319059016240974343962624, coefficient := (-17280319059016240974343962624) }, { argument := 1747455505338521750687761563648, coefficient := (-1747455505338521750687761563648) }, { argument := 188081036862823977676351471616, coefficient := (-188081036862823977676351471616) }, { argument := 16909963083961172183130214236160, coefficient := (-16909963083961172183130214236160) }, { argument := 117245321680721440629413904384, coefficient := (-117245321680721440629413904384) }, { argument := 6106527170870908366115307520, coefficient := (-6106527170870908366115307520) }, { argument := 186859731428649796003128410112, coefficient := (-186859731428649796003128410112) }, { argument := 195408869467869067715689840640, coefficient := (-195408869467869067715689840640) }, { argument := 117245321680721440629413904384, coefficient := (-117245321680721440629413904384) }, { argument := 2993419619160919281069723746304, coefficient := (-2993419619160919281069723746304) }, { argument := 191744953165346522696020656128, coefficient := (-191744953165346522696020656128) }, { argument := 1747455567803808870286730723328, coefficient := (-1747455567803808870286730723328) }, { argument := 186859731428649796003128410112, coefficient := (-186859731428649796003128410112) }, { argument := 6106527170870908366115307520, coefficient := (-6106527170870908366115307520) }, { argument := 191744953165346522696020656128, coefficient := (-191744953165346522696020656128) }, { argument := 6106527170870908366115307520, coefficient := (-6106527170870908366115307520) }, { argument := 186859731428649796003128410112, coefficient := (-186859731428649796003128410112) }, { argument := 195408869467869067715689840640, coefficient := (-195408869467869067715689840640) }, { argument := 17280319059016240974343962624, coefficient := (-17280319059016240974343962624) }, { argument := 1048613957896492088819712000, coefficient := (-1048613957896492088819712000) }, { argument := 183917036443141771641225216000, coefficient := (-183917036443141771641225216000) }, { argument := 183917058492765547247173632000, coefficient := (-183917058492765547247173632000) }, { argument := 1048591908272716482871296000, coefficient := (-1048591908272716482871296000) }, { argument := 1182003857326834322421841920, coefficient := (-1182003857326834322421841920) }, { argument := 380748689129304588024010506240, coefficient := (-380748689129304588024010506240) }, { argument := 4049422424509759659226454556672, coefficient := (-4049422424509759659226454556672) }, { argument := 380749836705865099513643925504, coefficient := (-380749836705865099513643925504) }, { argument := 1182003857326834322421841920, coefficient := (-1182003857326834322421841920) }, { argument := 42125680491431190874839580672, coefficient := (-42125680491431190874839580672) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 1666429956558678036836924784640, coefficient := (-1666429956558678036836924784640) }, { argument := 3184126436572101330012733440, coefficient := (-3184126436572101330012733440) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 1666429776104172562459656192000, coefficient := (-1666429776104172562459656192000) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 11696626479661060835059433472, coefficient := (-11696626479661060835059433472) }, { argument := 290198865105305437672046592, coefficient := (-290198865105305437672046592) }, { argument := 3184126436572101330012733440, coefficient := (-3184126436572101330012733440) }, { argument := 11696626479661060835059433472, coefficient := (-11696626479661060835059433472) }, { argument := 42125816559227164574919688192, coefficient := (-42125816559227164574919688192) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 290198865105305437672046592, coefficient := (-290198865105305437672046592) }, { argument := 282137785519046953292267520, coefficient := (-282137785519046953292267520) }, { argument := 69854038224602961511710720, coefficient := (-69854038224602961511710720) }, { argument := 22501477740145527752585379840, coefficient := (-22501477740145527752585379840) }, { argument := 239312678275848937870303690752, coefficient := (-239312678275848937870303690752) }, { argument := 22501545559600114745751896064, coefficient := (-22501545559600114745751896064) }, { argument := 69854038224602961511710720, coefficient := (-69854038224602961511710720) }, { argument := 10854403070435962178462810112, coefficient := (-10854403070435962178462810112) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }, { argument := 414171377311553624037811814400, coefficient := (-414171377311553624037811814400) }, { argument := 3547866714915135752597667840, coefficient := (-3547866714915135752597667840) }, { argument := 314367936764632281875742720, coefficient := (-314367936764632281875742720) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
