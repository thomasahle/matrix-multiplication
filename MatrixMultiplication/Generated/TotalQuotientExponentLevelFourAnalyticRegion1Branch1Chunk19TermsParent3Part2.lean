import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 19, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19

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
def constantNumerator : ℤ := 105020364421842568871109852840067072
def positiveArguments : Array ℕ := #[
    13947, 33, 99, 209, 539, 451,
    12617, 385, 451, 407, 209, 209,
    407, 12617, 407, 33, 539, 693,
    10395, 18249, 693, 5775, 693, 18249,
    36267, 5775, 559713, 35805, 10395, 18249,
    693, 35805, 693, 18249, 18249, 693,
    3753, 17097
  ]
def positiveCoefficients : Array ℕ := #[
    1104995182586444716417157475336192, 40852021296417549071671099392, 30639015972313161803753324544, 32341183526330559681739620352, 41703105073426248010664247296, 558310957717706503979505025024,
    976193092228977683025140645888, 29787932195304462864760176640, 558310957717706503979505025024, 31490099749321860742746472448, 32341183526330559681739620352, 32341183526330559681739620352,
    31490099749321860742746472448, 976193092228977683025140645888, 31490099749321860742746472448, 40852021296417549071671099392, 41703105073426248010664247296, 107236555903096066313136635904,
    1608548338546440994697049538560, 2823895972114863079579264745472, 107236555903096066313136635904, 1787275931718267771885610598400, 107236555903096066313136635904, 2823895972114863079579264745472,
    2806023212797680401860408639488, 1787275931718267771885610598400, 43305695825533628112788344799232, 2770277694163315046422696427520, 1608548338546440994697049538560, 2823895972114863079579264745472,
    107236555903096066313136635904, 2770277694163315046422696427520, 107236555903096066313136635904, 2823895972114863079579264745472, 2823895972114863079579264745472, 107236555903096066313136635904,
    1161497241859508042924103303168, 1322816303228884159996895428608
  ]
def positiveScales : Array ℕ := #[
    13, 5, 6, 7, 9, 8,
    13, 8, 8, 8, 7, 7,
    8, 13, 8, 5, 9, 9,
    13, 14, 9, 12, 9, 14,
    15, 12, 19, 15, 13, 14,
    9, 15, 9, 14, 14, 9,
    11, 14
  ]
def negativeArguments : Array ℕ := #[
    42571844245, 716112689, 594207118515, 594206976845, 209, 11500782939,
    11500780197, 209, 12699157591, 47174205785, 793530277, 302853950727,
    302853878521, 407, 302853950727, 302853878521, 12617, 407,
    9210476023615, 1393265, 9210475376833, 1393265, 4652795, 539,
    11, 231
  ]
def negativeCoefficients : Array ℕ := #[
    392655957766669915382570024960, 105679580015351689701744443392, 685074165126412839548501360640, 685074001792023281896490270720, 16170591763165279840869810176, 26518999940377271208329084928,
    26518993617755739944380268544, 16170591763165279840869810176, 117129055016441457966766358528, 435105250498201798126631649280, 117104399476470791291122221056, 698333665096601475152665903104,
    698333498600901151868680404992, 15745049874660930371373236224, 698333665096601475152665903104, 698333498600901151868680404992, 488096546114488841512570322944, 15745049874660930371373236224,
    41480296387857401716450263040, 51402405763713876864532480, 41480293475010227526506119168, 51402405763713876864532480, 21972203159663470902058680320, 20851552536713124005332123648,
    3486039150627630854115933814784, 73206822163180247936434610110464
  ]
def negativeScales : Array ℕ := #[
    35, 29, 39, 39, 7, 33,
    33, 7, 33, 35, 29, 38,
    38, 8, 38, 38, 13, 8,
    43, 20, 43, 20, 22, 9,
    3, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13767667211219704, 5044394119358453, 6629356620078832, 7707359132075544, 9074141462752505, 8816983623199035,
    13623081294652464, 8588714635582006, 8816983623199035, 8668884984264121, 7707359132075544, 7707359132075544,
    8668884984264121, 13623081294652464, 8668884984264121, 5044394119358453, 9074141462752505, 9436711542137211,
    13343602137745731, 14155529789593160, 9436711542137211, 12495605231190767, 9436711542137211, 14155529789593160,
    15146369790307684, 12495605231190767, 19094327730867403, 15127873446690294, 13343602137745731, 14155529789593160,
    9436711542137211, 15127873446690294, 9436711542137211, 14155529789593160, 14155529789593160, 9436711542137211,
    11873828574719291, 14061455578062747
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35309180539004601, 29415611389981114, 39112174932314948, 39112174588349647, 7707359132166870, 33421013027761882,
    33421012683796581, 7707359132166870, 33564013746692294, 35457279177993795, 29563710028972239, 38139831275217814,
    38139830931252512, 8668884984300449, 38139831275217814, 38139830931252512, 13623081294663700, 8668884984300449,
    43066412859477622, 20410038254991501, 43066412758168069, 20410038254991501, 22149666193342041, 9074141462752506,
    3459431618637364, 7851749043206919
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 6218640047 / 31250000000
noncomputable def negativeCeiling : ℝ := 9629374017 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 392655957766669915382570024960, coefficient := (-392655957766669915382570024960) }, { argument := 105679580015351689701744443392, coefficient := (-105679580015351689701744443392) }, { argument := 685074165126412839548501360640, coefficient := (-685074165126412839548501360640) }, { argument := 685074001792023281896490270720, coefficient := (-685074001792023281896490270720) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }, { argument := 26518999940377271208329084928, coefficient := (-26518999940377271208329084928) }, { argument := 26518993617755739944380268544, coefficient := (-26518993617755739944380268544) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }, { argument := 117129055016441457966766358528, coefficient := (-117129055016441457966766358528) }, { argument := 435105250498201798126631649280, coefficient := (-435105250498201798126631649280) }, { argument := 117104399476470791291122221056, coefficient := (-117104399476470791291122221056) }, { argument := 698333665096601475152665903104, coefficient := (-698333665096601475152665903104) }, { argument := 698333498600901151868680404992, coefficient := (-698333498600901151868680404992) }, { argument := 15745049874660930371373236224, coefficient := (-15745049874660930371373236224) }, { argument := 698333665096601475152665903104, coefficient := (-698333665096601475152665903104) }, { argument := 698333498600901151868680404992, coefficient := (-698333498600901151868680404992) }, { argument := 488096546114488841512570322944, coefficient := (-488096546114488841512570322944) }, { argument := 15745049874660930371373236224, coefficient := (-15745049874660930371373236224) }, { argument := 41480296387857401716450263040, coefficient := (-41480296387857401716450263040) }, { argument := 51402405763713876864532480, coefficient := (-51402405763713876864532480) }, { argument := 41480293475010227526506119168, coefficient := (-41480293475010227526506119168) }, { argument := 51402405763713876864532480, coefficient := (-51402405763713876864532480) }, { argument := 21972203159663470902058680320, coefficient := (-21972203159663470902058680320) }, { argument := 20851552536713124005332123648, coefficient := (-20851552536713124005332123648) }, { argument := 1104995182586444716417157475336192, coefficient := 1104995182586444716417157475336192 }, { argument := 40852021296417549071671099392, coefficient := 40852021296417549071671099392 }, { argument := 30639015972313161803753324544, coefficient := 30639015972313161803753324544 }, { argument := 32341183526330559681739620352, coefficient := 32341183526330559681739620352 }, { argument := 41703105073426248010664247296, coefficient := 41703105073426248010664247296 }, { argument := 558310957717706503979505025024, coefficient := 558310957717706503979505025024 }, { argument := 976193092228977683025140645888, coefficient := 976193092228977683025140645888 }, { argument := 29787932195304462864760176640, coefficient := 29787932195304462864760176640 }, { argument := 558310957717706503979505025024, coefficient := 558310957717706503979505025024 }, { argument := 31490099749321860742746472448, coefficient := 31490099749321860742746472448 }, { argument := 32341183526330559681739620352, coefficient := 32341183526330559681739620352 }, { argument := 32341183526330559681739620352, coefficient := 32341183526330559681739620352 }, { argument := 31490099749321860742746472448, coefficient := 31490099749321860742746472448 }, { argument := 976193092228977683025140645888, coefficient := 976193092228977683025140645888 }, { argument := 31490099749321860742746472448, coefficient := 31490099749321860742746472448 }, { argument := 40852021296417549071671099392, coefficient := 40852021296417549071671099392 }, { argument := 41703105073426248010664247296, coefficient := 41703105073426248010664247296 }, { argument := 3486039150627630854115933814784, coefficient := (-3486039150627630854115933814784) }, { argument := 107236555903096066313136635904, coefficient := 107236555903096066313136635904 }, { argument := 1608548338546440994697049538560, coefficient := 1608548338546440994697049538560 }, { argument := 2823895972114863079579264745472, coefficient := 2823895972114863079579264745472 }, { argument := 107236555903096066313136635904, coefficient := 107236555903096066313136635904 }, { argument := 1787275931718267771885610598400, coefficient := 1787275931718267771885610598400 }, { argument := 107236555903096066313136635904, coefficient := 107236555903096066313136635904 }, { argument := 2823895972114863079579264745472, coefficient := 2823895972114863079579264745472 }, { argument := 2806023212797680401860408639488, coefficient := 2806023212797680401860408639488 }, { argument := 1787275931718267771885610598400, coefficient := 1787275931718267771885610598400 }, { argument := 43305695825533628112788344799232, coefficient := 43305695825533628112788344799232 }, { argument := 2770277694163315046422696427520, coefficient := 2770277694163315046422696427520 }, { argument := 1608548338546440994697049538560, coefficient := 1608548338546440994697049538560 }, { argument := 2823895972114863079579264745472, coefficient := 2823895972114863079579264745472 }, { argument := 107236555903096066313136635904, coefficient := 107236555903096066313136635904 }, { argument := 2770277694163315046422696427520, coefficient := 2770277694163315046422696427520 }, { argument := 107236555903096066313136635904, coefficient := 107236555903096066313136635904 }, { argument := 2823895972114863079579264745472, coefficient := 2823895972114863079579264745472 }, { argument := 2823895972114863079579264745472, coefficient := 2823895972114863079579264745472 }, { argument := 107236555903096066313136635904, coefficient := 107236555903096066313136635904 }, { argument := 73206822163180247936434610110464, coefficient := (-73206822163180247936434610110464) }, { argument := 1161497241859508042924103303168, coefficient := 1161497241859508042924103303168 }, { argument := 1322816303228884159996895428608, coefficient := 1322816303228884159996895428608 }] }

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
def constantNumerator : ℤ := (-51096442280323905042773573724274688)
def positiveArguments : Array ℕ := #[
    417, 178893, 7923, 417, 7923, 15429,
    291483, 15429, 178893, 291483, 3753, 15429,
    15429, 17097, 637, 3185, 2639, 47411,
    17745, 637, 71071, 71071, 50869, 2639,
    305, 335, 305, 335, 59, 16995319755,
    16995319861, 17392333683, 63110901593, 4347955021, 1066584913, 41648210157,
    41648200209, 1066588593, 3162613, 200503159, 15422911267, 1604026749,
    3162613, 702407, 125126713, 62563363, 351197
  ]
def positiveCoefficients : Array ℕ := #[
    1032441992764007149265869602816, 13841175465492470844845564362752, 1226024866407258489753220153344, 1032441992764007149265869602816, 1226024866407258489753220153344, 1193761054133383266338661728256,
    45104809558877562333552678273024, 1193761054133383266338661728256, 13841175465492470844845564362752, 45104809558877562333552678273024, 1161497241859508042924103303168, 1193761054133383266338661728256,
    1193761054133383266338661728256, 1322816303228884159996895428608, 98570975628098404388842766336, 1971419512561968087776855326720, 102091367614816204545587150848, 1834124225079973881663824330752,
    2745905749639884122260619919360, 98570975628098404388842766336, 2749426141626601922417364303872, 2749426141626601922417364303872, 1967899120575250287620110942208, 102091367614816204545587150848,
    188785855991020491922116444160, 207354956580301196045603307520, 188785855991020491922116444160, 207354956580301196045603307520, 4674461588341595918019093069824, 80258128376664350390168825364480,
    80258128877235197574351218016256, 164265947286967945896849347444736, 596065612772935398656783423635456, 164261096481561475163025129340928, 10073609688571273061181629136896, 393356223433855848592080365420544,
    393356129477652305417619193724928, 10073644445188586981770401939456, 59740070517951269032890990592, 7574795182168666004442224525312, 72832639235553413658604661112832, 7574802157103961202908205154304,
    59740070517951269032890990592, 3317023274133018885616566272, 590894195582849513065963061248, 590894256973613790371350839296, 3316961883368741580228788224
  ]
def positiveScales : Array ℕ := #[
    8, 17, 12, 8, 12, 13,
    18, 13, 17, 18, 11, 13,
    13, 14, 9, 11, 11, 15,
    14, 9, 16, 16, 15, 11,
    8, 8, 8, 8, 5, 33,
    33, 34, 35, 32, 29, 35,
    35, 29, 21, 27, 33, 30,
    21, 19, 26, 25, 18
  ]
def negativeArguments : Array ℕ := #[
    417, 91, 5, 59, 1013, 5835,
    1273, 139, 15
  ]
def negativeCoefficients : Array ℕ := #[
    132152575073792915106031309160448, 14419525577596109442024998961152, 792281625142643375935439503360, 4674461588341595918019093069824, 160516257253899547964520043380736, 924592656541464819716657900421120,
    806859607045268014052651590221824, 88101716715861943404020872773632, 1188422437713965063903159255040
  ]
def negativeScales : Array ℕ := #[
    8, 6, 2, 5, 9, 12,
    10, 7, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8703903573439738, 17448737410944206, 12951831086224604, 8703903573439738, 12951831086224604, 13913356938731381,
    18153052218820099, 13913356938731381, 17448737410944206, 18153052218820099, 11873828574719291, 13913356938731381,
    13913356938731381, 14061455578062747, 9315149562256300, 11637077657142712, 11365775635326267, 15532934202477155,
    14115124953948306, 9315149562256300, 16116973378340675, 16116973378340675, 15634499113040997, 11365775635326267,
    8252665432450248, 8388017285345134, 8252665432450248, 8388017285345134, 5882643049164642, 33984418453165586,
    33984418462163691, 34017732473640310, 35877170182361168, 32017689869945805, 29990351678880469, 35277535445590386,
    35277535100991376, 29990356656551182, 21592685597471437, 27579049726141650, 33844356066431826, 30579051054586801,
    21592685597471437, 19421947696894029, 26898814578702574, 25898814728590907, 18421920995552654
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8703903573523992, 6507794640199048, 2321928094887363, 5882643052550791, 9984418477228694, 12510516940595095,
    10314016703901359, 7118941072723508, 3906890600547867
  ]

abbrev PositiveTerm := Fin 47
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 4303329021 / 5000000000
noncomputable def negativeCeiling : ℝ := 140815640203 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1032441992764007149265869602816, coefficient := 1032441992764007149265869602816 }, { argument := 13841175465492470844845564362752, coefficient := 13841175465492470844845564362752 }, { argument := 1226024866407258489753220153344, coefficient := 1226024866407258489753220153344 }, { argument := 1032441992764007149265869602816, coefficient := 1032441992764007149265869602816 }, { argument := 1226024866407258489753220153344, coefficient := 1226024866407258489753220153344 }, { argument := 1193761054133383266338661728256, coefficient := 1193761054133383266338661728256 }, { argument := 45104809558877562333552678273024, coefficient := 45104809558877562333552678273024 }, { argument := 1193761054133383266338661728256, coefficient := 1193761054133383266338661728256 }, { argument := 13841175465492470844845564362752, coefficient := 13841175465492470844845564362752 }, { argument := 45104809558877562333552678273024, coefficient := 45104809558877562333552678273024 }, { argument := 1161497241859508042924103303168, coefficient := 1161497241859508042924103303168 }, { argument := 1193761054133383266338661728256, coefficient := 1193761054133383266338661728256 }, { argument := 1193761054133383266338661728256, coefficient := 1193761054133383266338661728256 }, { argument := 1322816303228884159996895428608, coefficient := 1322816303228884159996895428608 }, { argument := 132152575073792915106031309160448, coefficient := (-132152575073792915106031309160448) }, { argument := 98570975628098404388842766336, coefficient := 98570975628098404388842766336 }, { argument := 1971419512561968087776855326720, coefficient := 1971419512561968087776855326720 }, { argument := 102091367614816204545587150848, coefficient := 102091367614816204545587150848 }, { argument := 1834124225079973881663824330752, coefficient := 1834124225079973881663824330752 }, { argument := 2745905749639884122260619919360, coefficient := 2745905749639884122260619919360 }, { argument := 98570975628098404388842766336, coefficient := 98570975628098404388842766336 }, { argument := 2749426141626601922417364303872, coefficient := 2749426141626601922417364303872 }, { argument := 2749426141626601922417364303872, coefficient := 2749426141626601922417364303872 }, { argument := 1967899120575250287620110942208, coefficient := 1967899120575250287620110942208 }, { argument := 102091367614816204545587150848, coefficient := 102091367614816204545587150848 }, { argument := 14419525577596109442024998961152, coefficient := (-14419525577596109442024998961152) }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 4674461588341595918019093069824, coefficient := 4674461588341595918019093069824 }, { argument := 4674461588341595918019093069824, coefficient := (-4674461588341595918019093069824) }, { argument := 80258128376664350390168825364480, coefficient := 80258128376664350390168825364480 }, { argument := 80258128877235197574351218016256, coefficient := 80258128877235197574351218016256 }, { argument := 160516257253899547964520043380736, coefficient := (-160516257253899547964520043380736) }, { argument := 164265947286967945896849347444736, coefficient := 164265947286967945896849347444736 }, { argument := 596065612772935398656783423635456, coefficient := 596065612772935398656783423635456 }, { argument := 164261096481561475163025129340928, coefficient := 164261096481561475163025129340928 }, { argument := 924592656541464819716657900421120, coefficient := (-924592656541464819716657900421120) }, { argument := 10073609688571273061181629136896, coefficient := 10073609688571273061181629136896 }, { argument := 393356223433855848592080365420544, coefficient := 393356223433855848592080365420544 }, { argument := 393356129477652305417619193724928, coefficient := 393356129477652305417619193724928 }, { argument := 10073644445188586981770401939456, coefficient := 10073644445188586981770401939456 }, { argument := 806859607045268014052651590221824, coefficient := (-806859607045268014052651590221824) }, { argument := 59740070517951269032890990592, coefficient := 59740070517951269032890990592 }, { argument := 7574795182168666004442224525312, coefficient := 7574795182168666004442224525312 }, { argument := 72832639235553413658604661112832, coefficient := 72832639235553413658604661112832 }, { argument := 7574802157103961202908205154304, coefficient := 7574802157103961202908205154304 }, { argument := 59740070517951269032890990592, coefficient := 59740070517951269032890990592 }, { argument := 88101716715861943404020872773632, coefficient := (-88101716715861943404020872773632) }, { argument := 3317023274133018885616566272, coefficient := 3317023274133018885616566272 }, { argument := 590894195582849513065963061248, coefficient := 590894195582849513065963061248 }, { argument := 590894256973613790371350839296, coefficient := 590894256973613790371350839296 }, { argument := 3316961883368741580228788224, coefficient := 3316961883368741580228788224 }, { argument := 1188422437713965063903159255040, coefficient := (-1188422437713965063903159255040) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19
