import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 17, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5977523606572433845791499007033344)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1816587, 1113, 10362869, 483, 93, 1929,
    969, 1816587, 1113, 93, 54010386891, 1160592959845,
    4508877875, 42383452025, 500485444125, 35169247425, 1160592733541, 500485444125,
    4508877875, 35169247425, 35169247425, 35169247425, 35169247425, 35169247425,
    54010613195, 42383452025, 49594309132521, 4990300083331051, 44225352535, 187758815683895605,
    1457978655, 3401950195, 44225352535, 44225352535, 1457978655, 545770009855,
    21869679825, 4990300084283371, 44225352535, 3401950195, 21869679825, 3401950195,
    44225352535, 44225352535, 214291879492559, 103487331, 10850460009, 116957113875,
    5425234143, 103487331, 5314434345733, 614695467, 188066166733307, 9673365507,
    291171537, 376118684763115, 291171537, 291171537, 24943695003, 291171537,
    9673365507, 24943695003, 10642517394965, 291171537
  ]
def negativeCoefficients : Array ℕ := #[
    8578589562016720189812375552, 43057101991394632686335164416, 97874530463937754852017307648, 37370314935927417048517312512, 1798881619586568211962789888, 37312286496585914848131416064,
    37486371814610421449289105408, 8578589562016720189812375552, 43057101991394632686335164416, 1798881619586568211962789888, 124539473037539288042786783232, 2676145163001222669857655357440,
    83174116219736366457552896000, 97729586558190230587624652800, 1154040862548842084598546432000, 2595032426055774633475650355200, 2676144641179726312761859244032, 1154040862548842084598546432000,
    83174116219736366457552896000, 81094763314242957296114073600, 81094763314242957296114073600, 81094763314242957296114073600, 2595032426055774633475650355200, 81094763314242957296114073600,
    124539994859035645138582896640, 97729586558190230587624652800, 55838228032229690581507375104, 5618578398939169105197949517824, 815813759782726945414378946560, 52849408271844867922534995066880,
    430319345819460366811980103680, 31377452299335651746706882560, 815813759782726945414378946560, 815813759782726945414378946560, 430319345819460366811980103680, 10067679694901124831871951175680,
    806848773411488187772462694400, 5618578400011386104482317205504, 815813759782726945414378946560, 31377452299335651746706882560, 806848773411488187772462694400, 31377452299335651746706882560,
    815813759782726945414378946560, 815813759782726945414378946560, 60317801789450746616248008704, 238625538728533595743322112, 25019457358505404761341165568, 269684743406478677753462784000,
    25019476443967992023086006272, 238625538728533595743322112, 191472676313024836071581548544, 11339129963018375252957724672, 6775797747368951809492098482176, 89221048919539321069325254656,
    10742333649175302871223107584, 6775551874184983062352400220160, 10742333649175302871223107584, 10742333649175302871223107584, 460129957973008806317389774848, 10742333649175302871223107584,
    89221048919539321069325254656, 460129957973008806317389774848, 191718549496993583211279810560, 10742333649175302871223107584
  ]
def negativeScales : Array ℕ := #[
    20, 10, 23, 8, 6, 10,
    9, 20, 10, 6, 35, 40,
    32, 35, 38, 35, 40, 38,
    32, 35, 35, 35, 35, 35,
    35, 35, 45, 52, 35, 57,
    30, 31, 35, 35, 30, 38,
    34, 52, 35, 31, 34, 31,
    35, 35, 47, 26, 33, 36,
    32, 26, 42, 29, 47, 33,
    28, 48, 28, 28, 34, 28,
    33, 34, 43, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20792799030852688, 10120237877341960, 23304920138187517, 8915879384625971, 6539158811108986, 10913637433615165,
    9920352861677847, 20792799030852688, 10120237877341960, 6539158811108986, 35652517831637784, 40077999221293034,
    32070121288442084, 35302782045232359, 38864537157072407, 35033595412416970, 40077998939981926, 38864537157072407,
    32070121288442084, 35033595412416970, 35033595412416970, 35033595412416970, 35033595412416970, 35033595412416970,
    35652523876530138, 35302782045232359, 45495239816702021, 52148047995529600, 35364154592037389, 57381658260078275,
    30441322452559881, 31663714873926383, 35364154592037389, 35364154592037389, 30441322452559881, 38989502184246767,
    34348213048168367, 52148047995804916, 35364154592037389, 31663714873926383, 34348213048168367, 31663714873926383,
    35364154592037389, 35364154592037389, 47606570509112590, 26624878921789179, 33337037156394529, 36767188659860633,
    32337038256917667, 26624878921789179, 42273053281950486, 29195296605222195, 47418233658536773, 33171370765976714,
    28117294093220921, 48418181306552189, 28117294093220921, 28117294093220921, 34537956141694563, 28117294093220921,
    33171370765976714, 34537956141694563, 43274904681711167, 28117294093220921
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
noncomputable def negativeCeiling : ℝ := 16593885399 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8578589562016720189812375552, coefficient := (-8578589562016720189812375552) }, { argument := 43057101991394632686335164416, coefficient := (-43057101991394632686335164416) }, { argument := 97874530463937754852017307648, coefficient := (-97874530463937754852017307648) }, { argument := 37370314935927417048517312512, coefficient := (-37370314935927417048517312512) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 37312286496585914848131416064, coefficient := (-37312286496585914848131416064) }, { argument := 37486371814610421449289105408, coefficient := (-37486371814610421449289105408) }, { argument := 8578589562016720189812375552, coefficient := (-8578589562016720189812375552) }, { argument := 43057101991394632686335164416, coefficient := (-43057101991394632686335164416) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 124539473037539288042786783232, coefficient := (-124539473037539288042786783232) }, { argument := 2676145163001222669857655357440, coefficient := (-2676145163001222669857655357440) }, { argument := 83174116219736366457552896000, coefficient := (-83174116219736366457552896000) }, { argument := 97729586558190230587624652800, coefficient := (-97729586558190230587624652800) }, { argument := 1154040862548842084598546432000, coefficient := (-1154040862548842084598546432000) }, { argument := 2595032426055774633475650355200, coefficient := (-2595032426055774633475650355200) }, { argument := 2676144641179726312761859244032, coefficient := (-2676144641179726312761859244032) }, { argument := 1154040862548842084598546432000, coefficient := (-1154040862548842084598546432000) }, { argument := 83174116219736366457552896000, coefficient := (-83174116219736366457552896000) }, { argument := 81094763314242957296114073600, coefficient := (-81094763314242957296114073600) }, { argument := 81094763314242957296114073600, coefficient := (-81094763314242957296114073600) }, { argument := 81094763314242957296114073600, coefficient := (-81094763314242957296114073600) }, { argument := 2595032426055774633475650355200, coefficient := (-2595032426055774633475650355200) }, { argument := 81094763314242957296114073600, coefficient := (-81094763314242957296114073600) }, { argument := 124539994859035645138582896640, coefficient := (-124539994859035645138582896640) }, { argument := 97729586558190230587624652800, coefficient := (-97729586558190230587624652800) }, { argument := 55838228032229690581507375104, coefficient := (-55838228032229690581507375104) }, { argument := 5618578398939169105197949517824, coefficient := (-5618578398939169105197949517824) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 52849408271844867922534995066880, coefficient := (-52849408271844867922534995066880) }, { argument := 430319345819460366811980103680, coefficient := (-430319345819460366811980103680) }, { argument := 31377452299335651746706882560, coefficient := (-31377452299335651746706882560) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 430319345819460366811980103680, coefficient := (-430319345819460366811980103680) }, { argument := 10067679694901124831871951175680, coefficient := (-10067679694901124831871951175680) }, { argument := 806848773411488187772462694400, coefficient := (-806848773411488187772462694400) }, { argument := 5618578400011386104482317205504, coefficient := (-5618578400011386104482317205504) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 31377452299335651746706882560, coefficient := (-31377452299335651746706882560) }, { argument := 806848773411488187772462694400, coefficient := (-806848773411488187772462694400) }, { argument := 31377452299335651746706882560, coefficient := (-31377452299335651746706882560) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 60317801789450746616248008704, coefficient := (-60317801789450746616248008704) }, { argument := 238625538728533595743322112, coefficient := (-238625538728533595743322112) }, { argument := 25019457358505404761341165568, coefficient := (-25019457358505404761341165568) }, { argument := 269684743406478677753462784000, coefficient := (-269684743406478677753462784000) }, { argument := 25019476443967992023086006272, coefficient := (-25019476443967992023086006272) }, { argument := 238625538728533595743322112, coefficient := (-238625538728533595743322112) }, { argument := 191472676313024836071581548544, coefficient := (-191472676313024836071581548544) }, { argument := 11339129963018375252957724672, coefficient := (-11339129963018375252957724672) }, { argument := 6775797747368951809492098482176, coefficient := (-6775797747368951809492098482176) }, { argument := 89221048919539321069325254656, coefficient := (-89221048919539321069325254656) }, { argument := 10742333649175302871223107584, coefficient := (-10742333649175302871223107584) }, { argument := 6775551874184983062352400220160, coefficient := (-6775551874184983062352400220160) }, { argument := 10742333649175302871223107584, coefficient := (-10742333649175302871223107584) }, { argument := 10742333649175302871223107584, coefficient := (-10742333649175302871223107584) }, { argument := 460129957973008806317389774848, coefficient := (-460129957973008806317389774848) }, { argument := 10742333649175302871223107584, coefficient := (-10742333649175302871223107584) }, { argument := 89221048919539321069325254656, coefficient := (-89221048919539321069325254656) }, { argument := 460129957973008806317389774848, coefficient := (-460129957973008806317389774848) }, { argument := 191718549496993583211279810560, coefficient := (-191718549496993583211279810560) }, { argument := 10742333649175302871223107584, coefficient := (-10742333649175302871223107584) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-43155677885589775188636394621763584)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    291171537, 614695467, 5813895, 609576405, 6570624375, 304788435,
    5813895, 620045297, 22470646799, 179765240455, 4960296313, 99156315264781,
    96810729, 5438805, 351931349405835, 294058057, 12394538840077, 294058057,
    294058057, 96810729, 5438805, 54010367541, 1160592944795, 4508875725,
    42383431815, 500485205475, 35169230655, 1160592718491, 500485205475, 4508875725,
    35169230655, 35169230655, 35169230655, 35169230655, 35169230655, 54010593845,
    42383431815, 44011549802313, 9018146716857223, 75908951209, 340498689280425827, 2502492897,
    5839150093, 75908951209, 75908951209, 2502492897, 936766507777, 37537393455,
    9018146724396423, 75908951209, 5839150093, 37537393455, 5839150093, 75908951209,
    75908951209, 379407431762461, 187979341288443, 22276767189, 6652625036150533, 350565967869,
    10552152879, 13304745759530581, 10552152879, 10552152879
  ]
def negativeCoefficients : Array ℕ := #[
    10742333649175302871223107584, 11339129963018375252957724672, 13405929142052449199063040, 1405587492050865436030402560, 15150828281262847064801280000, 1405588564267864720398090240,
    13405929142052449199063040, 11437816907866228823479549952, 414510270671873756075795677184, 414510423002780473760059228160, 11437664576959511139215998976, 55820043059737392002128412672,
    223230342681531428276011008, 12541030487726484734607360, 198119736755514291856626155520, 339025857518205970658885632, 55820040501599916913372168192, 339025857518205970658885632,
    339025857518205970658885632, 223230342681531428276011008, 12541030487726484734607360, 124539428419477059757808812032, 2676145128298285381191561379840, 83174076559236607982016921600,
    97729539957103014378869882880, 1154040312259407935750484787200, 2595031188648182169038927953920, 2676144606476789024095765266432, 1154040312259407935750484787200, 83174076559236607982016921600,
    81094724645255692782466498560, 81094724645255692782466498560, 81094724645255692782466498560, 2595031188648182169038927953920, 81094724645255692782466498560, 124539950240973416853604925440,
    97729539957103014378869882880, 198210399289694853692808757248, 20307061096805325700532277346304, 2800545991712256506512422207488, 191683721270433506907750897025024, 1477211072551519915523035889664,
    107713307373548327173554700288, 2800545991712256506512422207488, 2800545991712256506512422207488, 1477211072551519915523035889664, 34560584051569934690257693835264, 2769770761034099841605692293120,
    20307061113782094855868099067904, 2800545991712256506512422207488, 107713307373548327173554700288, 2769770761034099841605692293120, 107713307373548327173554700288, 2800545991712256506512422207488,
    2800545991712256506512422207488, 213587396038377031005038968832, 6772669531039865505926111821824, 410933823125093136955210727424, 239686077070745383200358550994944, 3233400345115864419726526513152,
    389305727171140866589147004928, 239676992179524445486465316552704, 389305727171140866589147004928, 389305727171140866589147004928
  ]
def negativeScales : Array ℕ := #[
    28, 29, 22, 29, 32, 28,
    22, 29, 34, 37, 32, 46,
    26, 22, 48, 28, 43, 28,
    28, 26, 22, 35, 40, 32,
    35, 38, 35, 40, 38, 32,
    35, 35, 35, 35, 35, 35,
    35, 45, 53, 36, 58, 31,
    32, 36, 36, 31, 39, 35,
    53, 36, 32, 35, 32, 36,
    36, 48, 47, 34, 52, 38,
    33, 53, 33, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28117294093220921, 29195296605222195, 22471073585699149, 29183231820315493, 32613383323463827, 28183232920838631,
    22471073585699149, 29207798373582553, 34387322600773730, 37387323130958430, 32207779159382070, 46494769894149774,
    26528663606519469, 22374858270439748, 48322287360890519, 28131525779048500, 43494769828033517, 28131525779048500,
    28131525779048500, 26528663606519469, 22374858270439748, 35652517314771388, 40077999202584872, 32070120600511480,
    35302781357301756, 38864536469141775, 35033594724486366, 40077998921273761, 38864536469141775, 32070120600511480,
    35033594724486366, 35033594724486366, 35033594724486366, 35033594724486366, 35033594724486366, 35652523359665907,
    35302781357301756, 45322947408557060, 53001752404782931, 36143550967628999, 58240426857806298, 31220718828151459,
    32443111249487943, 36143550967628999, 36143550967628999, 31220718828151459, 39768898540168921, 35127609423759978,
    53001752405989029, 36143550967628999, 32443111249487943, 35127609423759978, 32443111249487943, 36143550967628999,
    36143550967628999, 48430741266692355, 47417567448526111, 34374820832413370, 52562845144281656, 38350894993167888,
    33296818320412095, 53562790460354777, 33296818320412095, 33296818320412095
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
noncomputable def negativeCeiling : ℝ := 126732505449 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 10742333649175302871223107584, coefficient := (-10742333649175302871223107584) }, { argument := 11339129963018375252957724672, coefficient := (-11339129963018375252957724672) }, { argument := 13405929142052449199063040, coefficient := (-13405929142052449199063040) }, { argument := 1405587492050865436030402560, coefficient := (-1405587492050865436030402560) }, { argument := 15150828281262847064801280000, coefficient := (-15150828281262847064801280000) }, { argument := 1405588564267864720398090240, coefficient := (-1405588564267864720398090240) }, { argument := 13405929142052449199063040, coefficient := (-13405929142052449199063040) }, { argument := 11437816907866228823479549952, coefficient := (-11437816907866228823479549952) }, { argument := 414510270671873756075795677184, coefficient := (-414510270671873756075795677184) }, { argument := 414510423002780473760059228160, coefficient := (-414510423002780473760059228160) }, { argument := 11437664576959511139215998976, coefficient := (-11437664576959511139215998976) }, { argument := 55820043059737392002128412672, coefficient := (-55820043059737392002128412672) }, { argument := 223230342681531428276011008, coefficient := (-223230342681531428276011008) }, { argument := 12541030487726484734607360, coefficient := (-12541030487726484734607360) }, { argument := 198119736755514291856626155520, coefficient := (-198119736755514291856626155520) }, { argument := 339025857518205970658885632, coefficient := (-339025857518205970658885632) }, { argument := 55820040501599916913372168192, coefficient := (-55820040501599916913372168192) }, { argument := 339025857518205970658885632, coefficient := (-339025857518205970658885632) }, { argument := 339025857518205970658885632, coefficient := (-339025857518205970658885632) }, { argument := 223230342681531428276011008, coefficient := (-223230342681531428276011008) }, { argument := 12541030487726484734607360, coefficient := (-12541030487726484734607360) }, { argument := 124539428419477059757808812032, coefficient := (-124539428419477059757808812032) }, { argument := 2676145128298285381191561379840, coefficient := (-2676145128298285381191561379840) }, { argument := 83174076559236607982016921600, coefficient := (-83174076559236607982016921600) }, { argument := 97729539957103014378869882880, coefficient := (-97729539957103014378869882880) }, { argument := 1154040312259407935750484787200, coefficient := (-1154040312259407935750484787200) }, { argument := 2595031188648182169038927953920, coefficient := (-2595031188648182169038927953920) }, { argument := 2676144606476789024095765266432, coefficient := (-2676144606476789024095765266432) }, { argument := 1154040312259407935750484787200, coefficient := (-1154040312259407935750484787200) }, { argument := 83174076559236607982016921600, coefficient := (-83174076559236607982016921600) }, { argument := 81094724645255692782466498560, coefficient := (-81094724645255692782466498560) }, { argument := 81094724645255692782466498560, coefficient := (-81094724645255692782466498560) }, { argument := 81094724645255692782466498560, coefficient := (-81094724645255692782466498560) }, { argument := 2595031188648182169038927953920, coefficient := (-2595031188648182169038927953920) }, { argument := 81094724645255692782466498560, coefficient := (-81094724645255692782466498560) }, { argument := 124539950240973416853604925440, coefficient := (-124539950240973416853604925440) }, { argument := 97729539957103014378869882880, coefficient := (-97729539957103014378869882880) }, { argument := 198210399289694853692808757248, coefficient := (-198210399289694853692808757248) }, { argument := 20307061096805325700532277346304, coefficient := (-20307061096805325700532277346304) }, { argument := 2800545991712256506512422207488, coefficient := (-2800545991712256506512422207488) }, { argument := 191683721270433506907750897025024, coefficient := (-191683721270433506907750897025024) }, { argument := 1477211072551519915523035889664, coefficient := (-1477211072551519915523035889664) }, { argument := 107713307373548327173554700288, coefficient := (-107713307373548327173554700288) }, { argument := 2800545991712256506512422207488, coefficient := (-2800545991712256506512422207488) }, { argument := 2800545991712256506512422207488, coefficient := (-2800545991712256506512422207488) }, { argument := 1477211072551519915523035889664, coefficient := (-1477211072551519915523035889664) }, { argument := 34560584051569934690257693835264, coefficient := (-34560584051569934690257693835264) }, { argument := 2769770761034099841605692293120, coefficient := (-2769770761034099841605692293120) }, { argument := 20307061113782094855868099067904, coefficient := (-20307061113782094855868099067904) }, { argument := 2800545991712256506512422207488, coefficient := (-2800545991712256506512422207488) }, { argument := 107713307373548327173554700288, coefficient := (-107713307373548327173554700288) }, { argument := 2769770761034099841605692293120, coefficient := (-2769770761034099841605692293120) }, { argument := 107713307373548327173554700288, coefficient := (-107713307373548327173554700288) }, { argument := 2800545991712256506512422207488, coefficient := (-2800545991712256506512422207488) }, { argument := 2800545991712256506512422207488, coefficient := (-2800545991712256506512422207488) }, { argument := 213587396038377031005038968832, coefficient := (-213587396038377031005038968832) }, { argument := 6772669531039865505926111821824, coefficient := (-6772669531039865505926111821824) }, { argument := 410933823125093136955210727424, coefficient := (-410933823125093136955210727424) }, { argument := 239686077070745383200358550994944, coefficient := (-239686077070745383200358550994944) }, { argument := 3233400345115864419726526513152, coefficient := (-3233400345115864419726526513152) }, { argument := 389305727171140866589147004928, coefficient := (-389305727171140866589147004928) }, { argument := 239676992179524445486465316552704, coefficient := (-239676992179524445486465316552704) }, { argument := 389305727171140866589147004928, coefficient := (-389305727171140866589147004928) }, { argument := 389305727171140866589147004928, coefficient := (-389305727171140866589147004928) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
