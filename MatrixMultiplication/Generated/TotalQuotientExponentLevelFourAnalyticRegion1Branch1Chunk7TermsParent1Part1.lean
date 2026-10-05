import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

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
def constantNumerator : ℤ := (-17253787469923461335411869534388224)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    273938826819, 6999849405, 522432862195, 1940707891325, 32645180665, 927398386970009,
    975061575, 927398888174183, 975061575, 46291519435, 171961458725, 2892610945,
    94950642633, 94950665271, 1171437, 867688532276191, 2892610945, 62482680958109095,
    32645180665, 2892610945, 3905167222105885, 2892610945, 2892610945, 119919385177,
    743814243, 32645180665, 119919385177, 1735382956007627, 2892610945, 743814243,
    2892610945, 31215569053268723, 43028775279, 1116515127, 112687701668716255, 69309823653,
    15611483047523095, 69309823653, 72229940139, 43028775279, 2147144475, 14643207627662775,
    37012559925, 14643216875244105, 37012559925, 46291519435, 171961458725, 2892610945,
    3699375687, 3699376569, 13342739, 6165626145, 6165627615, 851,
    412485, 195012315, 7402511985, 780049795, 412485, 6999849405,
    273938826819, 273938826819, 6999849405, 46291519435
  ]
def negativeCoefficients : Array ℕ := #[
    631659928772791928880195698688, 16140553816067885127759298560, 1204648163075841887732120944640, 4474967724137600535899825766400, 1204394585934532778480925409280, 2088315514991065792682741727232,
    8993355665066575745620377600, 2088316643602531424151361552384, 8993355665066575745620377600, 106740976475074597647149957120, 396516127455230427231630131200, 106718507614452271510968074240,
    875765102142603123064741822464, 875765310941299293383156563968, 22127819302373474320785604608, 976930437658176594758739165184, 106718507614452271510968074240, 35174622335006213278945394032640,
    1204394585934532778480925409280, 106718507614452271510968074240, 35174619292591077351252473937920, 106718507614452271510968074240, 106718507614452271510968074240, 4424244415673435598926133592064,
    109767607832008050696995733504, 1204394585934532778480925409280, 4424244415673435598926133592064, 976933754252632351253016346624, 106718507614452271510968074240, 109767607832008050696995733504,
    106718507614452271510968074240, 35145606289114751876381542449152, 396870402688436654200357650432, 20596068802194317383651295232, 126875072811117036576072395653120, 639270289360415928023330586624,
    35153934617762912969530340802560, 639270289360415928023330586624, 666203610101746958448105357312, 396870402688436654200357650432, 19803912309802228253510860800, 16486786103862719556250868121600,
    85345152556164174529010073600, 16486796515713677522839818731520, 85345152556164174529010073600, 106740976475074597647149957120, 396516127455230427231630131200, 106718507614452271510968074240,
    545931492244739609183215681536, 545931622404965793277811884032, 252037213773110588435779813376, 28433931887746854644959150080, 28433938666925301733219368960, 16460733959872790842799292416,
    60872041833952675186606080, 7194684532053260596496302080, 68276122044931339623208058880, 7194689466557300313801359360, 60872041833952675186606080, 16140553816067885127759298560,
    631659928772791928880195698688, 631659928772791928880195698688, 16140553816067885127759298560, 106740976475074597647149957120
  ]
def negativeScales : Array ℕ := #[
    37, 32, 38, 40, 34, 49,
    29, 49, 29, 35, 37, 31,
    36, 36, 20, 49, 31, 55,
    34, 31, 51, 31, 31, 36,
    29, 34, 36, 50, 31, 29,
    31, 54, 35, 30, 56, 36,
    53, 36, 36, 35, 30, 53,
    35, 53, 35, 35, 37, 31,
    31, 31, 23, 32, 32, 9,
    18, 27, 32, 29, 18, 32,
    37, 37, 32, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37995062827081033, 32704676738267960, 38926454699208425, 40819720124507129, 34926150981451746, 49720182545964459,
    29860918088955285, 49720183325655898, 29860918088955285, 35430028866123530, 37323294297426971, 31429725148403493,
    36466458713548690, 36466459057513992, 20159847937326706, 49624170590480057, 31429725148403493, 55794305875613561,
    34926150981451746, 31429725148403493, 51794305750828214, 31429725148403493, 31429725148403493, 36803273936215774,
    29470367132900915, 34926150981451746, 36803273936215774, 50624175488296799, 31429725148403493, 29470367132900915,
    31429725148403493, 54793115284820626, 35324582726551007, 30056355651496890, 56645107686646851, 36012340796633578,
    53793457114610123, 36012340796633578, 36071877923610942, 35324582726551007, 30999772146721039, 53701081132115238,
    35107295870066533, 53701082043215857, 35107295870066533, 35430028866123530, 37323294297426971, 31429725148403493,
    31784634674045595, 31784635018010901, 23669551517882943, 32521600267741615, 32521600611706917, 9733015321840403,
    18653982131227114, 27538989991938486, 32785367775657142, 29538990981416487, 18653982131227114, 32704676738267960,
    37995062827081033, 37995062827081033, 32704676738267960, 35430028866123530
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
noncomputable def negativeCeiling : ℝ := 21557305063 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 631659928772791928880195698688, coefficient := (-631659928772791928880195698688) }, { argument := 16140553816067885127759298560, coefficient := (-16140553816067885127759298560) }, { argument := 1204648163075841887732120944640, coefficient := (-1204648163075841887732120944640) }, { argument := 4474967724137600535899825766400, coefficient := (-4474967724137600535899825766400) }, { argument := 1204394585934532778480925409280, coefficient := (-1204394585934532778480925409280) }, { argument := 2088315514991065792682741727232, coefficient := (-2088315514991065792682741727232) }, { argument := 8993355665066575745620377600, coefficient := (-8993355665066575745620377600) }, { argument := 2088316643602531424151361552384, coefficient := (-2088316643602531424151361552384) }, { argument := 8993355665066575745620377600, coefficient := (-8993355665066575745620377600) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }, { argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 875765102142603123064741822464, coefficient := (-875765102142603123064741822464) }, { argument := 875765310941299293383156563968, coefficient := (-875765310941299293383156563968) }, { argument := 22127819302373474320785604608, coefficient := (-22127819302373474320785604608) }, { argument := 976930437658176594758739165184, coefficient := (-976930437658176594758739165184) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 35174622335006213278945394032640, coefficient := (-35174622335006213278945394032640) }, { argument := 1204394585934532778480925409280, coefficient := (-1204394585934532778480925409280) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 35174619292591077351252473937920, coefficient := (-35174619292591077351252473937920) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 4424244415673435598926133592064, coefficient := (-4424244415673435598926133592064) }, { argument := 109767607832008050696995733504, coefficient := (-109767607832008050696995733504) }, { argument := 1204394585934532778480925409280, coefficient := (-1204394585934532778480925409280) }, { argument := 4424244415673435598926133592064, coefficient := (-4424244415673435598926133592064) }, { argument := 976933754252632351253016346624, coefficient := (-976933754252632351253016346624) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 109767607832008050696995733504, coefficient := (-109767607832008050696995733504) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 35145606289114751876381542449152, coefficient := (-35145606289114751876381542449152) }, { argument := 396870402688436654200357650432, coefficient := (-396870402688436654200357650432) }, { argument := 20596068802194317383651295232, coefficient := (-20596068802194317383651295232) }, { argument := 126875072811117036576072395653120, coefficient := (-126875072811117036576072395653120) }, { argument := 639270289360415928023330586624, coefficient := (-639270289360415928023330586624) }, { argument := 35153934617762912969530340802560, coefficient := (-35153934617762912969530340802560) }, { argument := 639270289360415928023330586624, coefficient := (-639270289360415928023330586624) }, { argument := 666203610101746958448105357312, coefficient := (-666203610101746958448105357312) }, { argument := 396870402688436654200357650432, coefficient := (-396870402688436654200357650432) }, { argument := 19803912309802228253510860800, coefficient := (-19803912309802228253510860800) }, { argument := 16486786103862719556250868121600, coefficient := (-16486786103862719556250868121600) }, { argument := 85345152556164174529010073600, coefficient := (-85345152556164174529010073600) }, { argument := 16486796515713677522839818731520, coefficient := (-16486796515713677522839818731520) }, { argument := 85345152556164174529010073600, coefficient := (-85345152556164174529010073600) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }, { argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 545931492244739609183215681536, coefficient := (-545931492244739609183215681536) }, { argument := 545931622404965793277811884032, coefficient := (-545931622404965793277811884032) }, { argument := 252037213773110588435779813376, coefficient := (-252037213773110588435779813376) }, { argument := 28433931887746854644959150080, coefficient := (-28433931887746854644959150080) }, { argument := 28433938666925301733219368960, coefficient := (-28433938666925301733219368960) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 60872041833952675186606080, coefficient := (-60872041833952675186606080) }, { argument := 7194684532053260596496302080, coefficient := (-7194684532053260596496302080) }, { argument := 68276122044931339623208058880, coefficient := (-68276122044931339623208058880) }, { argument := 7194689466557300313801359360, coefficient := (-7194689466557300313801359360) }, { argument := 60872041833952675186606080, coefficient := (-60872041833952675186606080) }, { argument := 16140553816067885127759298560, coefficient := (-16140553816067885127759298560) }, { argument := 631659928772791928880195698688, coefficient := (-631659928772791928880195698688) }, { argument := 631659928772791928880195698688, coefficient := (-631659928772791928880195698688) }, { argument := 16140553816067885127759298560, coefficient := (-16140553816067885127759298560) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }] }

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
def constantNumerator : ℤ := (-6662771095213651119958815114526720)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    171961458725, 2892610945, 7294762515, 285480239597, 285480239597, 7294762515,
    1919114134291, 7129030760285, 119919385177, 188668160037, 188668205019, 11903533569,
    44218660815, 743814243, 6165626145, 6165627615, 69, 4345631415,
    170066111817, 170066111817, 4345631415, 522432862195, 1940707891325, 32645180665,
    3699375687, 3699376569, 1919114134291, 7129030760285, 119919385177, 3022389936279,
    3022390656873, 14789, 193600660953, 193600707111, 26749, 1734140947683969,
    1099497105, 28529865, 392376114642477, 1771046235, 1734477256704687, 1771046235,
    1845662805, 1099497105, 54865125, 927398620160409, 3900248975, 927399121364583,
    3900248975, 53370957, 188668160037, 188668205019, 14789, 437,
    216847875, 8486332925, 8486332925, 216847875, 46291519435, 171961458725,
    2892610945, 6165626145, 6165627615, 11903533569
  ]
def negativeCoefficients : Array ℕ := #[
    396516127455230427231630131200, 106718507614452271510968074240, 16820577149086854265731809280, 658272614743392827990389817344, 658272614743392827990389817344, 16820577149086854265731809280,
    4425175910438092605314702508032, 16438425741072552854659866296320, 4424244415673435598926133592064, 870078315765053752135749992448, 870078523207914233036512690176, 109790718660076729008497098752,
    407845159668237010866819563520, 109767607832008050696995733504, 909885820407899348638692802560, 909886037341609655463019806720, 21354465677672809742009892864, 10020343818897162886006702080,
    392145755037383836888448630784, 392145755037383836888448630784, 10020343818897162886006702080, 1204648163075841887732120944640, 4474967724137600535899825766400, 1204394585934532778480925409280,
    545931492244739609183215681536, 545931622404965793277811884032, 4425175910438092605314702508032, 16438425741072552854659866296320, 4424244415673435598926133592064, 13938313411373508146958975369216,
    13938316734526782909624134664192, 286060863140492013835674189824, 892825461275251235851717312512, 892825674141454474423088185344, 517400907981947452707448029184, 976234565724680198354085347328,
    10141070852859779306320035840, 526283118112483556815011840, 3534209847385884873053316317184, 16335018319875931936527482880, 976423890872228563506476089344, 16335018319875931936527482880,
    17023234705099948895439421440, 10141070852859779306320035840, 506041459723541881552896000, 2088316040089165065871196946432, 8993361833196625392251699200, 2088317168700630697339816771584,
    8993361833196625392251699200, 252037218495477071305425027072, 870078315765053752135749992448, 870078523207914233036512690176, 286060863140492013835674189824, 16905618661490974379091165184,
    500017156631594954391552000, 19568151448971249345730969600, 19568151448971249345730969600, 500017156631594954391552000, 106740976475074597647149957120, 396516127455230427231630131200,
    106718507614452271510968074240, 28433931887746854644959150080, 28433938666925301733219368960, 109790718660076729008497098752
  ]
def negativeScales : Array ℕ := #[
    37, 31, 32, 38, 38, 32,
    40, 42, 36, 37, 37, 33,
    35, 29, 32, 32, 6, 32,
    37, 37, 32, 38, 40, 34,
    31, 31, 40, 42, 36, 41,
    41, 13, 37, 37, 14, 50,
    30, 24, 48, 30, 50, 30,
    30, 30, 25, 49, 31, 49,
    31, 25, 37, 37, 13, 8,
    27, 32, 32, 27, 35, 37,
    31, 32, 32, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37323294297426971, 31429725148403493, 32764213865470397, 38054599932179107, 38054599932179107, 32764213865470397,
    40803577653940080, 42696843084615943, 36803273936215774, 37457060015546416, 37457060359511718, 33470670850620953,
    35363936281924318, 29470367132900915, 32521600267741615, 32521600611706917, 6108524456778170, 32016918668104613,
    37307304735119171, 37307304735119171, 32016918668104613, 38926454699208425, 40819720124507129, 34926150981451746,
    31784634674045595, 31784635018010901, 40803577653940080, 42696843084615943, 36803273936215774, 41458826941720608,
    41458827285685910, 13852236885192533, 37494292921745554, 37494293265710856, 14707197337615895, 50623142586160325,
    30034196659536449, 24765969584799886, 48479230550572464, 30721954729739330, 50623422346762077, 30721954729739330,
    30781491857037243, 30034196659536449, 25709386056206097, 49720182908723977, 31860919078433326, 49720183688415220,
    31860919078433326, 25669551544914406, 37457060015546416, 37457060359511718, 13852236885192533, 8771489469857739,
    27692108064744185, 32982494149559077, 32982494149559077, 27692108064744185, 35430028866123530, 37323294297426971,
    31429725148403493, 32521600267741615, 32521600611706917, 33470670850620953
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
noncomputable def negativeCeiling : ℝ := 1678158507 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 16820577149086854265731809280, coefficient := (-16820577149086854265731809280) }, { argument := 658272614743392827990389817344, coefficient := (-658272614743392827990389817344) }, { argument := 658272614743392827990389817344, coefficient := (-658272614743392827990389817344) }, { argument := 16820577149086854265731809280, coefficient := (-16820577149086854265731809280) }, { argument := 4425175910438092605314702508032, coefficient := (-4425175910438092605314702508032) }, { argument := 16438425741072552854659866296320, coefficient := (-16438425741072552854659866296320) }, { argument := 4424244415673435598926133592064, coefficient := (-4424244415673435598926133592064) }, { argument := 870078315765053752135749992448, coefficient := (-870078315765053752135749992448) }, { argument := 870078523207914233036512690176, coefficient := (-870078523207914233036512690176) }, { argument := 109790718660076729008497098752, coefficient := (-109790718660076729008497098752) }, { argument := 407845159668237010866819563520, coefficient := (-407845159668237010866819563520) }, { argument := 109767607832008050696995733504, coefficient := (-109767607832008050696995733504) }, { argument := 909885820407899348638692802560, coefficient := (-909885820407899348638692802560) }, { argument := 909886037341609655463019806720, coefficient := (-909886037341609655463019806720) }, { argument := 21354465677672809742009892864, coefficient := (-21354465677672809742009892864) }, { argument := 10020343818897162886006702080, coefficient := (-10020343818897162886006702080) }, { argument := 392145755037383836888448630784, coefficient := (-392145755037383836888448630784) }, { argument := 392145755037383836888448630784, coefficient := (-392145755037383836888448630784) }, { argument := 10020343818897162886006702080, coefficient := (-10020343818897162886006702080) }, { argument := 1204648163075841887732120944640, coefficient := (-1204648163075841887732120944640) }, { argument := 4474967724137600535899825766400, coefficient := (-4474967724137600535899825766400) }, { argument := 1204394585934532778480925409280, coefficient := (-1204394585934532778480925409280) }, { argument := 545931492244739609183215681536, coefficient := (-545931492244739609183215681536) }, { argument := 545931622404965793277811884032, coefficient := (-545931622404965793277811884032) }, { argument := 4425175910438092605314702508032, coefficient := (-4425175910438092605314702508032) }, { argument := 16438425741072552854659866296320, coefficient := (-16438425741072552854659866296320) }, { argument := 4424244415673435598926133592064, coefficient := (-4424244415673435598926133592064) }, { argument := 13938313411373508146958975369216, coefficient := (-13938313411373508146958975369216) }, { argument := 13938316734526782909624134664192, coefficient := (-13938316734526782909624134664192) }, { argument := 286060863140492013835674189824, coefficient := (-286060863140492013835674189824) }, { argument := 892825461275251235851717312512, coefficient := (-892825461275251235851717312512) }, { argument := 892825674141454474423088185344, coefficient := (-892825674141454474423088185344) }, { argument := 517400907981947452707448029184, coefficient := (-517400907981947452707448029184) }, { argument := 976234565724680198354085347328, coefficient := (-976234565724680198354085347328) }, { argument := 10141070852859779306320035840, coefficient := (-10141070852859779306320035840) }, { argument := 526283118112483556815011840, coefficient := (-526283118112483556815011840) }, { argument := 3534209847385884873053316317184, coefficient := (-3534209847385884873053316317184) }, { argument := 16335018319875931936527482880, coefficient := (-16335018319875931936527482880) }, { argument := 976423890872228563506476089344, coefficient := (-976423890872228563506476089344) }, { argument := 16335018319875931936527482880, coefficient := (-16335018319875931936527482880) }, { argument := 17023234705099948895439421440, coefficient := (-17023234705099948895439421440) }, { argument := 10141070852859779306320035840, coefficient := (-10141070852859779306320035840) }, { argument := 506041459723541881552896000, coefficient := (-506041459723541881552896000) }, { argument := 2088316040089165065871196946432, coefficient := (-2088316040089165065871196946432) }, { argument := 8993361833196625392251699200, coefficient := (-8993361833196625392251699200) }, { argument := 2088317168700630697339816771584, coefficient := (-2088317168700630697339816771584) }, { argument := 8993361833196625392251699200, coefficient := (-8993361833196625392251699200) }, { argument := 252037218495477071305425027072, coefficient := (-252037218495477071305425027072) }, { argument := 870078315765053752135749992448, coefficient := (-870078315765053752135749992448) }, { argument := 870078523207914233036512690176, coefficient := (-870078523207914233036512690176) }, { argument := 286060863140492013835674189824, coefficient := (-286060863140492013835674189824) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 500017156631594954391552000, coefficient := (-500017156631594954391552000) }, { argument := 19568151448971249345730969600, coefficient := (-19568151448971249345730969600) }, { argument := 19568151448971249345730969600, coefficient := (-19568151448971249345730969600) }, { argument := 500017156631594954391552000, coefficient := (-500017156631594954391552000) }, { argument := 106740976475074597647149957120, coefficient := (-106740976475074597647149957120) }, { argument := 396516127455230427231630131200, coefficient := (-396516127455230427231630131200) }, { argument := 106718507614452271510968074240, coefficient := (-106718507614452271510968074240) }, { argument := 28433931887746854644959150080, coefficient := (-28433931887746854644959150080) }, { argument := 28433938666925301733219368960, coefficient := (-28433938666925301733219368960) }, { argument := 109790718660076729008497098752, coefficient := (-109790718660076729008497098752) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
