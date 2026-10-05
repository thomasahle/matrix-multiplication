import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-318102635374237271352788907982848)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3187, 2957, 3187, 2957, 68579961761935, 8840403355,
    413689517784945, 1713331795, 870615725, 27411373745, 9363604495, 68845589491855,
    8840403355, 838190465, 34257316226031, 1674019203333137, 1759746255, 1571713851,
    71706791799, 20760514263, 837009774026091, 71706791799, 1759746255, 1758615759,
    756841707, 1758615759, 20760514263, 756841707, 17128485753493, 1571713851,
    48645, 37835, 5405, 50807, 599955, 42159,
    37835, 599955, 5405, 42159, 42159, 42159,
    42159, 42159, 48645, 50807, 555539460713, 65959581090617,
    196775901, 673491786596547, 201920369, 6430585, 196775901, 111892179,
    201920369, 3152272767, 3858351, 32979799128985, 196775901, 6430585,
    3858351, 6430585, 99031009, 111892179
  ]
def negativeCoefficients : Array ℕ := #[
    61645545393789170876617326592, 57196698377607335513698598912, 61645545393789170876617326592, 57196698377607335513698598912, 77214172559033332577798717440, 163076658198048287401632071680,
    931545979071679239898382991360, 252843145085715187031091445760, 8030012732811047359794380800, 252825298091408173961272360960, 172728015726701368836012113920, 77513242795405078265614827520,
    163076658198048287401632071680, 7730942496439301671978270720, 19285154573783307240364572672, 942389032542771296087251615744, 8115397200163456853496299520, 7248250791625366806466658304,
    330689209165731981831538999296, 95740973362039467410825674752, 942389226602341622276406902784, 330689209165731981831538999296, 8115397200163456853496299520, 8110183707566368765180379136,
    6980632636669235433629024256, 8110183707566368765180379136, 95740973362039467410825674752, 6980632636669235433629024256, 19284960514212981051209285632, 7248250791625366806466658304,
    229719517559193891420241920, 178670735879373026660188160, 204195126719283459040215040, 239929273895158064372252672, 2833207383230057994182983680, 6370887953641643922054709248,
    178670735879373026660188160, 2833207383230057994182983680, 204195126719283459040215040, 199090248551301372564209664, 199090248551301372564209664, 199090248551301372564209664,
    6370887953641643922054709248, 199090248551301372564209664, 229719517559193891420241920, 239929273895158064372252672, 312740913532084137760915456, 37131943102652091919451029504,
    907468671405151857886101504, 379142169894162335206855409664, 931193342552998965281816576, 29655838934808884244643840, 907468671405151857886101504, 516011597465674585856802816,
    931193342552998965281816576, 14537292245843315056724410368, 569392107548330577497161728, 37131952767012663636671856640, 907468671405151857886101504, 29655838934808884244643840,
    569392107548330577497161728, 29655838934808884244643840, 913399839192113634735030272, 516011597465674585856802816
  ]
def negativeScales : Array ℕ := #[
    11, 11, 11, 11, 45, 33,
    48, 30, 29, 34, 33, 45,
    33, 29, 44, 50, 30, 30,
    36, 34, 49, 36, 30, 30,
    29, 30, 34, 29, 43, 30,
    15, 15, 12, 15, 19, 15,
    15, 19, 12, 15, 15, 15,
    15, 15, 15, 15, 39, 45,
    27, 49, 27, 22, 27, 26,
    27, 31, 21, 44, 27, 22,
    21, 22, 26, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11637983303793500, 11529918528121040, 11637983303793500, 11529918528121040, 45962852346336958, 33041465049958469,
    48555541730930575, 30674157417384555, 29697460837384599, 34674055580813323, 33124416852388293, 45968429480552566,
    33041465049958469, 29642702869018110, 44961477378941487, 50572237501018816, 30712720269852486, 30549691435883801,
    36061390720948405, 34273123130309811, 49572237798102866, 36061390720948405, 30712720269852486, 30711793156027240,
    29495416352036672, 30711793156027240, 34273123130309811, 29495416352036672, 43961462861544375, 30549691435883801,
    15570003904066736, 15207433824679617, 12400078902622020, 15632739659425936, 19194494768972119, 15363553026596901,
    15207433824679617, 19194494768972119, 12400078902622020, 15363553026596901, 15363553026596901, 15363553026596901,
    15363553026596901, 15363553026596901, 15570003904066736, 15632739659425936, 39015098435578788, 45906647474700197,
    27551978304794339, 49258653680185361, 27589211210996085, 22616518556996512, 27551978304794339, 26737533958119835,
    27589211210996085, 31553745230968604, 21879552965834572, 44906647850191575, 27551978304794339, 22616518556996512,
    21879552965834572, 22616518556996512, 26561377002797047, 26737533958119835
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
noncomputable def negativeCeiling : ℝ := 2888965919 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 61645545393789170876617326592, coefficient := (-61645545393789170876617326592) }, { argument := 57196698377607335513698598912, coefficient := (-57196698377607335513698598912) }, { argument := 61645545393789170876617326592, coefficient := (-61645545393789170876617326592) }, { argument := 57196698377607335513698598912, coefficient := (-57196698377607335513698598912) }, { argument := 77214172559033332577798717440, coefficient := (-77214172559033332577798717440) }, { argument := 163076658198048287401632071680, coefficient := (-163076658198048287401632071680) }, { argument := 931545979071679239898382991360, coefficient := (-931545979071679239898382991360) }, { argument := 252843145085715187031091445760, coefficient := (-252843145085715187031091445760) }, { argument := 8030012732811047359794380800, coefficient := (-8030012732811047359794380800) }, { argument := 252825298091408173961272360960, coefficient := (-252825298091408173961272360960) }, { argument := 172728015726701368836012113920, coefficient := (-172728015726701368836012113920) }, { argument := 77513242795405078265614827520, coefficient := (-77513242795405078265614827520) }, { argument := 163076658198048287401632071680, coefficient := (-163076658198048287401632071680) }, { argument := 7730942496439301671978270720, coefficient := (-7730942496439301671978270720) }, { argument := 19285154573783307240364572672, coefficient := (-19285154573783307240364572672) }, { argument := 942389032542771296087251615744, coefficient := (-942389032542771296087251615744) }, { argument := 8115397200163456853496299520, coefficient := (-8115397200163456853496299520) }, { argument := 7248250791625366806466658304, coefficient := (-7248250791625366806466658304) }, { argument := 330689209165731981831538999296, coefficient := (-330689209165731981831538999296) }, { argument := 95740973362039467410825674752, coefficient := (-95740973362039467410825674752) }, { argument := 942389226602341622276406902784, coefficient := (-942389226602341622276406902784) }, { argument := 330689209165731981831538999296, coefficient := (-330689209165731981831538999296) }, { argument := 8115397200163456853496299520, coefficient := (-8115397200163456853496299520) }, { argument := 8110183707566368765180379136, coefficient := (-8110183707566368765180379136) }, { argument := 6980632636669235433629024256, coefficient := (-6980632636669235433629024256) }, { argument := 8110183707566368765180379136, coefficient := (-8110183707566368765180379136) }, { argument := 95740973362039467410825674752, coefficient := (-95740973362039467410825674752) }, { argument := 6980632636669235433629024256, coefficient := (-6980632636669235433629024256) }, { argument := 19284960514212981051209285632, coefficient := (-19284960514212981051209285632) }, { argument := 7248250791625366806466658304, coefficient := (-7248250791625366806466658304) }, { argument := 229719517559193891420241920, coefficient := (-229719517559193891420241920) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 204195126719283459040215040, coefficient := (-204195126719283459040215040) }, { argument := 239929273895158064372252672, coefficient := (-239929273895158064372252672) }, { argument := 2833207383230057994182983680, coefficient := (-2833207383230057994182983680) }, { argument := 6370887953641643922054709248, coefficient := (-6370887953641643922054709248) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 2833207383230057994182983680, coefficient := (-2833207383230057994182983680) }, { argument := 204195126719283459040215040, coefficient := (-204195126719283459040215040) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 6370887953641643922054709248, coefficient := (-6370887953641643922054709248) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 229719517559193891420241920, coefficient := (-229719517559193891420241920) }, { argument := 239929273895158064372252672, coefficient := (-239929273895158064372252672) }, { argument := 312740913532084137760915456, coefficient := (-312740913532084137760915456) }, { argument := 37131943102652091919451029504, coefficient := (-37131943102652091919451029504) }, { argument := 907468671405151857886101504, coefficient := (-907468671405151857886101504) }, { argument := 379142169894162335206855409664, coefficient := (-379142169894162335206855409664) }, { argument := 931193342552998965281816576, coefficient := (-931193342552998965281816576) }, { argument := 29655838934808884244643840, coefficient := (-29655838934808884244643840) }, { argument := 907468671405151857886101504, coefficient := (-907468671405151857886101504) }, { argument := 516011597465674585856802816, coefficient := (-516011597465674585856802816) }, { argument := 931193342552998965281816576, coefficient := (-931193342552998965281816576) }, { argument := 14537292245843315056724410368, coefficient := (-14537292245843315056724410368) }, { argument := 569392107548330577497161728, coefficient := (-569392107548330577497161728) }, { argument := 37131952767012663636671856640, coefficient := (-37131952767012663636671856640) }, { argument := 907468671405151857886101504, coefficient := (-907468671405151857886101504) }, { argument := 29655838934808884244643840, coefficient := (-29655838934808884244643840) }, { argument := 569392107548330577497161728, coefficient := (-569392107548330577497161728) }, { argument := 29655838934808884244643840, coefficient := (-29655838934808884244643840) }, { argument := 913399839192113634735030272, coefficient := (-913399839192113634735030272) }, { argument := 516011597465674585856802816, coefficient := (-516011597465674585856802816) }] }

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
def constantNumerator : ℤ := (-8725825996908709477510317120421888)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    555532235369, 3187, 2957, 3187, 2957, 116384073696625,
    242701462927, 703619186399119, 188175904357, 23902770635, 752650690943, 257080149343,
    116840000472433, 242701462927, 23012288651, 619579636569379, 30073875688192733, 64454018865,
    57097928901, 2671118038153, 728103792937, 15036940999065131, 2671118038153, 64454018865,
    64453147441, 27625205013, 64453147441, 728103792937, 27625205013, 309786663315925,
    57097928901, 1203705, 936215, 133745, 1257203, 14845695,
    1043211, 936215, 14845695, 133745, 1043211, 1043211,
    1043211, 1043211, 1043211, 1203705, 1257203, 8244686637581,
    3591009192621881, 31414720257, 36562213001184675, 32236020133, 1026624845, 31414720257,
    17863272303, 32236020133, 503251499019, 615974907, 897752615096495, 31414720257,
    1026624845, 615974907, 1026624845, 15810022613
  ]
def negativeCoefficients : Array ℕ := #[
    312736846025015884804784128, 61645545393789170876617326592, 57196698377607335513698598912, 61645545393789170876617326592, 57196698377607335513698598912, 262073635465990347463589888000,
    559631471616159462112052117504, 3168819105677803895612740993024, 867808187128106285772442697728, 27558018284776559117871349760, 867747167045386534055070138368, 592786465170168966180855873536,
    263100291294808917698762768384, 559631471616159462112052117504, 26531362455957988882698469376, 697584655095050650263010410496, 33860173835732852822470811451392, 297241697631175597597088808960,
    263317720393902770373739413504, 12318357710119384184416802701312, 3357786081851512808823794434048, 33860180940090928906347885887488, 12318357710119384184416802701312, 297241697631175597597088808960,
    297237678897298675529011953664, 254797543429284573404152725504, 297237678897298675529011953664, 3357786081851512808823794434048, 254797543429284573404152725504, 697577550736974566385935974400,
    263317720393902770373739413504, 5684336147262606291951943680, 4421150336759804893740400640, 5052743242011205592846172160, 5936973309363166571594252288, 70106812482905477600740638720,
    157645589150749614496800571392, 4421150336759804893740400640, 70106812482905477600740638720, 5052743242011205592846172160, 4926424660960925453025017856, 4926424660960925453025017856,
    4926424660960925453025017856, 157645589150749614496800571392, 4926424660960925453025017856, 5684336147262606291951943680, 5936973309363166571594252288, 37130767668796299202764210176,
    4043116915443982241367005855744, 144874826182014538071385571328, 41165392211994001639050785587200, 148662403337099885471944671232, 4734471443856684250698874880, 144874826182014538071385571328,
    82379803123106305962160422912, 148662403337099885471944671232, 2320837901778546619692588466176, 90901851722048337613418397696, 4043118342819463203890156011520, 144874826182014538071385571328,
    4734471443856684250698874880, 90901851722048337613418397696, 4734471443856684250698874880, 145821720470785874921525346304
  ]
def negativeScales : Array ℕ := #[
    39, 11, 11, 11, 11, 46,
    37, 49, 37, 34, 39, 37,
    46, 37, 34, 49, 54, 35,
    35, 41, 39, 53, 41, 35,
    35, 34, 35, 39, 34, 48,
    35, 20, 19, 17, 20, 23,
    19, 19, 23, 17, 19, 19,
    19, 19, 19, 20, 20, 42,
    51, 34, 55, 34, 29, 34,
    34, 34, 38, 29, 49, 34,
    29, 29, 29, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39015079671770846, 11637983303793500, 11529918528121040, 11637983303793500, 11529918528121040, 46725886978115846,
    37820391849355301, 49321788151405581, 37453290948712602, 34476458803469040, 39453189501794692, 37903427263982597,
    46731527597685596, 37820391849355301, 34421685420538800, 49138283056954772, 54739360321632806, 35907551270811095,
    35732719365045167, 41280580869505401, 39405353168473391, 53739360624331226, 41280580869505401, 35907551270811095,
    35907531765313753, 34685266120040113, 35907531765313753, 39405353168473391, 34685266120040113, 48138268364151136,
    35732719365045167, 20199050433859907, 19836480355810319, 17029125432417594, 20261786189207869, 23823541299803889,
    19992599577423370, 19836480355810319, 23823541299803889, 17029125432417594, 19992599577423370, 19992599577423370,
    19992599577423370, 19992599577423370, 19992599577423370, 20199050433859907, 20261786189207869, 42906601804599404,
    51673310769509880, 34870721684608192, 55021202913243967, 34907954593281557, 29935261942353534, 34870721684608192,
    34056277335205052, 34907954593281557, 38872488610867750, 29198296340077480, 49673311278836523, 34870721684608192,
    29935261942353534, 29198296340077480, 29935261942353534, 33880120383095956
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
noncomputable def negativeCeiling : ℝ := 9912767587 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 312736846025015884804784128, coefficient := (-312736846025015884804784128) }, { argument := 61645545393789170876617326592, coefficient := (-61645545393789170876617326592) }, { argument := 57196698377607335513698598912, coefficient := (-57196698377607335513698598912) }, { argument := 61645545393789170876617326592, coefficient := (-61645545393789170876617326592) }, { argument := 57196698377607335513698598912, coefficient := (-57196698377607335513698598912) }, { argument := 262073635465990347463589888000, coefficient := (-262073635465990347463589888000) }, { argument := 559631471616159462112052117504, coefficient := (-559631471616159462112052117504) }, { argument := 3168819105677803895612740993024, coefficient := (-3168819105677803895612740993024) }, { argument := 867808187128106285772442697728, coefficient := (-867808187128106285772442697728) }, { argument := 27558018284776559117871349760, coefficient := (-27558018284776559117871349760) }, { argument := 867747167045386534055070138368, coefficient := (-867747167045386534055070138368) }, { argument := 592786465170168966180855873536, coefficient := (-592786465170168966180855873536) }, { argument := 263100291294808917698762768384, coefficient := (-263100291294808917698762768384) }, { argument := 559631471616159462112052117504, coefficient := (-559631471616159462112052117504) }, { argument := 26531362455957988882698469376, coefficient := (-26531362455957988882698469376) }, { argument := 697584655095050650263010410496, coefficient := (-697584655095050650263010410496) }, { argument := 33860173835732852822470811451392, coefficient := (-33860173835732852822470811451392) }, { argument := 297241697631175597597088808960, coefficient := (-297241697631175597597088808960) }, { argument := 263317720393902770373739413504, coefficient := (-263317720393902770373739413504) }, { argument := 12318357710119384184416802701312, coefficient := (-12318357710119384184416802701312) }, { argument := 3357786081851512808823794434048, coefficient := (-3357786081851512808823794434048) }, { argument := 33860180940090928906347885887488, coefficient := (-33860180940090928906347885887488) }, { argument := 12318357710119384184416802701312, coefficient := (-12318357710119384184416802701312) }, { argument := 297241697631175597597088808960, coefficient := (-297241697631175597597088808960) }, { argument := 297237678897298675529011953664, coefficient := (-297237678897298675529011953664) }, { argument := 254797543429284573404152725504, coefficient := (-254797543429284573404152725504) }, { argument := 297237678897298675529011953664, coefficient := (-297237678897298675529011953664) }, { argument := 3357786081851512808823794434048, coefficient := (-3357786081851512808823794434048) }, { argument := 254797543429284573404152725504, coefficient := (-254797543429284573404152725504) }, { argument := 697577550736974566385935974400, coefficient := (-697577550736974566385935974400) }, { argument := 263317720393902770373739413504, coefficient := (-263317720393902770373739413504) }, { argument := 5684336147262606291951943680, coefficient := (-5684336147262606291951943680) }, { argument := 4421150336759804893740400640, coefficient := (-4421150336759804893740400640) }, { argument := 5052743242011205592846172160, coefficient := (-5052743242011205592846172160) }, { argument := 5936973309363166571594252288, coefficient := (-5936973309363166571594252288) }, { argument := 70106812482905477600740638720, coefficient := (-70106812482905477600740638720) }, { argument := 157645589150749614496800571392, coefficient := (-157645589150749614496800571392) }, { argument := 4421150336759804893740400640, coefficient := (-4421150336759804893740400640) }, { argument := 70106812482905477600740638720, coefficient := (-70106812482905477600740638720) }, { argument := 5052743242011205592846172160, coefficient := (-5052743242011205592846172160) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 157645589150749614496800571392, coefficient := (-157645589150749614496800571392) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 5684336147262606291951943680, coefficient := (-5684336147262606291951943680) }, { argument := 5936973309363166571594252288, coefficient := (-5936973309363166571594252288) }, { argument := 37130767668796299202764210176, coefficient := (-37130767668796299202764210176) }, { argument := 4043116915443982241367005855744, coefficient := (-4043116915443982241367005855744) }, { argument := 144874826182014538071385571328, coefficient := (-144874826182014538071385571328) }, { argument := 41165392211994001639050785587200, coefficient := (-41165392211994001639050785587200) }, { argument := 148662403337099885471944671232, coefficient := (-148662403337099885471944671232) }, { argument := 4734471443856684250698874880, coefficient := (-4734471443856684250698874880) }, { argument := 144874826182014538071385571328, coefficient := (-144874826182014538071385571328) }, { argument := 82379803123106305962160422912, coefficient := (-82379803123106305962160422912) }, { argument := 148662403337099885471944671232, coefficient := (-148662403337099885471944671232) }, { argument := 2320837901778546619692588466176, coefficient := (-2320837901778546619692588466176) }, { argument := 90901851722048337613418397696, coefficient := (-90901851722048337613418397696) }, { argument := 4043118342819463203890156011520, coefficient := (-4043118342819463203890156011520) }, { argument := 144874826182014538071385571328, coefficient := (-144874826182014538071385571328) }, { argument := 4734471443856684250698874880, coefficient := (-4734471443856684250698874880) }, { argument := 90901851722048337613418397696, coefficient := (-90901851722048337613418397696) }, { argument := 4734471443856684250698874880, coefficient := (-4734471443856684250698874880) }, { argument := 145821720470785874921525346304, coefficient := (-145821720470785874921525346304) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
