import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-844957558450688656141731158294528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5843046825, 60901099875, 5843046825, 79123275, 391241515, 14178722005,
    113429817725, 3129890435, 89399025, 6601884075, 68810333625, 6601884075,
    89399025, 4415439955, 160017005485, 1280136514325, 35323049195, 6908108031,
    11708310273, 6908108031, 167674935, 6076595145, 48612779025, 1341381615,
    4613965587, 7820048621, 4613965587, 489, 489, 402369974963,
    38635964661593, 313739199, 382256131667555, 321941531, 10252915, 313739199,
    178400721, 321941531, 5025978933, 6151749, 19317990351471, 313739199,
    10252915, 6151749, 10252915, 157894891, 178400721, 402369974963,
    4742622610151, 56762041, 82949910501045, 1404558589, 44685011, 82949944021011,
    22946357, 22946357, 776553029, 42269605, 1404558589, 776553029,
    4742567747465, 44685011, 42269605, 56762041
  ]
def negativeCoefficients : Array ℕ := #[
    215570378782952323084084838400, 2246854006403099529414967296000, 215570378782952323084084838400, 1459566804198741122639462400, 7217132098215396644214538240, 261551256118508961476462510080,
    261551352237574800549294899200, 7217035979149557571382149120, 824560467307081023828787200, 121783265935823714989060915200, 1269326614006945838046117888000, 121783265935823714989060915200,
    824560467307081023828787200, 81450490822716619270421217280, 2951792747623172565234362613760, 2951793832395487034770613862400, 81449406050402149734169968640, 127432100881394609479898628096,
    431960406283230824807673102336, 127432100881394609479898628096, 6186113227041768552183889920, 224186790958721966979825008640, 224186873346492686185109913600, 6186030839271049346898984960,
    85112642348292062589424238592, 288508871111104602938458243072, 85112642348292062589424238592, 9458635612664858662901121024, 9458635612664858662901121024, 226514158663555325630611456,
    21750114506631235798634070016, 1446866677460907920663248896, 215191071517260994220035932160, 1484693257263807474144641024, 47283224753624441851740160, 1446866677460907920663248896,
    822728110713065288220278784, 1484693257263807474144641024, 23178236774226701395723026432, 907837915269589283553411072, 21750123537107908163643899904, 1446866677460907920663248896,
    47283224753624441851740160, 907837915269589283553411072, 47283224753624441851740160, 1456323322411632809033596928, 822728110713065288220278784, 226514158663555325630611456,
    10679436709917466360123752448, 261768710857102147729752064, 373573186022922255151210168320, 6477383206953399953397907456, 206073240461974031191506944, 373573336983428642222905491456,
    211642787501486842845331456, 211642787501486842845331456, 3581218746406737893409161216, 194934146382948407883857920, 6477383206953399953397907456, 3581218746406737893409161216,
    10679313170131353287859896320, 206073240461974031191506944, 194934146382948407883857920, 261768710857102147729752064
  ]
def negativeScales : Array ℕ := #[
    32, 35, 32, 26, 28, 33,
    36, 31, 26, 32, 36, 32,
    26, 32, 37, 40, 35, 32,
    33, 32, 27, 32, 35, 30,
    32, 32, 32, 8, 8, 38,
    45, 28, 48, 28, 23, 28,
    27, 28, 32, 22, 44, 28,
    23, 22, 23, 27, 27, 38,
    42, 25, 46, 30, 25, 46,
    24, 24, 29, 25, 30, 29,
    42, 25, 25, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32444073704782960, 35825749233422188, 32444073704782960, 26237598806290293, 28543484223221510, 33723008450534821,
    36723008980719522, 31543465009021026, 26413755761444132, 32620230659946553, 36001906187493695, 32620230659946553,
    26413755761444132, 32039910049339919, 37219434276531092, 40219434806715792, 35039890835139436, 32685643498365071,
    33446813832000410, 32685643498365071, 27321091801883972, 32500616029075422, 35500616559260122, 30321072587683489,
    32103360097788348, 32864530433755024, 32103360097788348, 8933690662845865, 8933690662845865, 38549731698338875,
    45135009653104716, 28224990551812153, 48441532972077008, 28262223458011129, 23289530804006864, 28224990551812153,
    27410546204968240, 28262223458011129, 32226757477986341, 22552565209842095, 44135010252100238, 28224990551812153,
    23289530804006864, 22552565209842095, 23289530804006864, 27234389249814403, 27410546204968240, 38549731698338875,
    42108822210497066, 25758423129983616, 46237305658119282, 30387469659509166, 25413287643664905, 46237306241110616,
    24451761791479579, 24451761791479579, 29532509205364667, 25333117294980911, 30387469659509166, 29532509205364667,
    42108805521295893, 25413287643664905, 25333117294980911, 25758423129983616
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
noncomputable def negativeCeiling : ℝ := 6068727727 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 215570378782952323084084838400, coefficient := (-215570378782952323084084838400) }, { argument := 2246854006403099529414967296000, coefficient := (-2246854006403099529414967296000) }, { argument := 215570378782952323084084838400, coefficient := (-215570378782952323084084838400) }, { argument := 1459566804198741122639462400, coefficient := (-1459566804198741122639462400) }, { argument := 7217132098215396644214538240, coefficient := (-7217132098215396644214538240) }, { argument := 261551256118508961476462510080, coefficient := (-261551256118508961476462510080) }, { argument := 261551352237574800549294899200, coefficient := (-261551352237574800549294899200) }, { argument := 7217035979149557571382149120, coefficient := (-7217035979149557571382149120) }, { argument := 824560467307081023828787200, coefficient := (-824560467307081023828787200) }, { argument := 121783265935823714989060915200, coefficient := (-121783265935823714989060915200) }, { argument := 1269326614006945838046117888000, coefficient := (-1269326614006945838046117888000) }, { argument := 121783265935823714989060915200, coefficient := (-121783265935823714989060915200) }, { argument := 824560467307081023828787200, coefficient := (-824560467307081023828787200) }, { argument := 81450490822716619270421217280, coefficient := (-81450490822716619270421217280) }, { argument := 2951792747623172565234362613760, coefficient := (-2951792747623172565234362613760) }, { argument := 2951793832395487034770613862400, coefficient := (-2951793832395487034770613862400) }, { argument := 81449406050402149734169968640, coefficient := (-81449406050402149734169968640) }, { argument := 127432100881394609479898628096, coefficient := (-127432100881394609479898628096) }, { argument := 431960406283230824807673102336, coefficient := (-431960406283230824807673102336) }, { argument := 127432100881394609479898628096, coefficient := (-127432100881394609479898628096) }, { argument := 6186113227041768552183889920, coefficient := (-6186113227041768552183889920) }, { argument := 224186790958721966979825008640, coefficient := (-224186790958721966979825008640) }, { argument := 224186873346492686185109913600, coefficient := (-224186873346492686185109913600) }, { argument := 6186030839271049346898984960, coefficient := (-6186030839271049346898984960) }, { argument := 85112642348292062589424238592, coefficient := (-85112642348292062589424238592) }, { argument := 288508871111104602938458243072, coefficient := (-288508871111104602938458243072) }, { argument := 85112642348292062589424238592, coefficient := (-85112642348292062589424238592) }, { argument := 9458635612664858662901121024, coefficient := (-9458635612664858662901121024) }, { argument := 9458635612664858662901121024, coefficient := (-9458635612664858662901121024) }, { argument := 226514158663555325630611456, coefficient := (-226514158663555325630611456) }, { argument := 21750114506631235798634070016, coefficient := (-21750114506631235798634070016) }, { argument := 1446866677460907920663248896, coefficient := (-1446866677460907920663248896) }, { argument := 215191071517260994220035932160, coefficient := (-215191071517260994220035932160) }, { argument := 1484693257263807474144641024, coefficient := (-1484693257263807474144641024) }, { argument := 47283224753624441851740160, coefficient := (-47283224753624441851740160) }, { argument := 1446866677460907920663248896, coefficient := (-1446866677460907920663248896) }, { argument := 822728110713065288220278784, coefficient := (-822728110713065288220278784) }, { argument := 1484693257263807474144641024, coefficient := (-1484693257263807474144641024) }, { argument := 23178236774226701395723026432, coefficient := (-23178236774226701395723026432) }, { argument := 907837915269589283553411072, coefficient := (-907837915269589283553411072) }, { argument := 21750123537107908163643899904, coefficient := (-21750123537107908163643899904) }, { argument := 1446866677460907920663248896, coefficient := (-1446866677460907920663248896) }, { argument := 47283224753624441851740160, coefficient := (-47283224753624441851740160) }, { argument := 907837915269589283553411072, coefficient := (-907837915269589283553411072) }, { argument := 47283224753624441851740160, coefficient := (-47283224753624441851740160) }, { argument := 1456323322411632809033596928, coefficient := (-1456323322411632809033596928) }, { argument := 822728110713065288220278784, coefficient := (-822728110713065288220278784) }, { argument := 226514158663555325630611456, coefficient := (-226514158663555325630611456) }, { argument := 10679436709917466360123752448, coefficient := (-10679436709917466360123752448) }, { argument := 261768710857102147729752064, coefficient := (-261768710857102147729752064) }, { argument := 373573186022922255151210168320, coefficient := (-373573186022922255151210168320) }, { argument := 6477383206953399953397907456, coefficient := (-6477383206953399953397907456) }, { argument := 206073240461974031191506944, coefficient := (-206073240461974031191506944) }, { argument := 373573336983428642222905491456, coefficient := (-373573336983428642222905491456) }, { argument := 211642787501486842845331456, coefficient := (-211642787501486842845331456) }, { argument := 211642787501486842845331456, coefficient := (-211642787501486842845331456) }, { argument := 3581218746406737893409161216, coefficient := (-3581218746406737893409161216) }, { argument := 194934146382948407883857920, coefficient := (-194934146382948407883857920) }, { argument := 6477383206953399953397907456, coefficient := (-6477383206953399953397907456) }, { argument := 3581218746406737893409161216, coefficient := (-3581218746406737893409161216) }, { argument := 10679313170131353287859896320, coefficient := (-10679313170131353287859896320) }, { argument := 206073240461974031191506944, coefficient := (-206073240461974031191506944) }, { argument := 194934146382948407883857920, coefficient := (-194934146382948407883857920) }, { argument := 261768710857102147729752064, coefficient := (-261768710857102147729752064) }] }

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

end TermShard6


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 39770424910504137961177259832246272
def positiveArguments : Array ℕ := #[
    223, 1, 1, 40819847, 1108490145, 326558759,
    605217377, 141, 10489269475, 3489, 111, 10489273821,
    57, 57, 1929, 105, 3489, 1929,
    605210655, 111, 105, 141, 15596997, 2582886109,
    137547, 24458833455, 141143, 4495, 137547, 78213,
    141143, 2203449, 2697, 80715231, 137547, 4495,
    2697, 4495, 69223, 78213, 15596997, 334066421,
    9194671371
  ]
def positiveCoefficients : Array ℕ := #[
    565372167701790313067529629597696, 79228162514264337593543950336, 79228162514264337593543950336, 1542130218469336308538824196096, 5234696707339313039028435025920, 1542130138189106099754855563264,
    2858058255995082109153697595392, 87274772769619309380388257792, 99068349197055359888202609459200, 2159586398533345889561522208768, 68705672180338605256901394432, 99068390243864828991158806904832,
    70562582239266675669250080768, 70562582239266675669250080768, 1193993167890749275140205314048, 64991852062482464432204021760, 2159586398533345889561522208768, 1193993167890749275140205314048,
    2858026512247584259398571130880, 68705672180338605256901394432, 64991852062482464432204021760, 87274772769619309380388257792, 589237886929747262312646967296, 48789339160844772320854939795456,
    5321091830737068770985932488704, 462014301271931051026913395998720, 5460205342651763379377721573376, 173891889893368260489736355840, 5321091830737068770985932488704, 3025718884144607732521412591616,
    5460205342651763379377721573376, 85241804425729121292068761632768, 3338724285952670601402938032128, 48789363396029562407874176483328, 5321091830737068770985932488704, 173891889893368260489736355840,
    3338724285952670601402938032128, 173891889893368260489736355840, 5355870208715742423083879759872, 3025718884144607732521412591616, 589237886929747262312646967296, 1577584069582620186079202902016,
    43420607903411488771297788297216
  ]
def positiveScales : Array ℕ := #[
    7, 0, 0, 25, 30, 28,
    29, 7, 33, 11, 6, 33,
    5, 5, 10, 6, 11, 10,
    29, 6, 6, 7, 23, 31,
    17, 34, 17, 12, 17, 16,
    17, 21, 11, 26, 17, 12,
    11, 12, 16, 16, 23, 28,
    33
  ]
def negativeArguments : Array ℕ := #[
    783500498097, 21377239784699, 6268002549117, 346528199, 12558296633, 100466409985,
    2772188671, 4288676733, 7268727939, 4288676733, 535, 535,
    25680699, 43525317, 25680699, 489, 489, 1,
    105, 2665, 1091
  ]
def negativeCoefficients : Array ℕ := #[
    14114290205096988841447784448, 48137264564290079269272420352, 14114286972280320125898326016, 6392317001276494170590019584, 231659683990679365879152508928, 231659769124709109057946910720,
    6392231867246750991795617792, 79112122108523791015401750528, 268168728064310586404763598848, 79112122108523791015401750528, 10348405015901225735484866560, 10348405015901225735484866560,
    3789802256695750467803676672, 12846406134817273600228196352, 3789802256695750467803676672, 9458635612664858662901121024, 9458635612664858662901121024, 158456325028528675187087900672,
    8318957063997755447322114785280, 211143053100514459686794627645440, 691503402424499138516451598532608
  ]
def negativeScales : Array ℕ := #[
    39, 44, 42, 28, 33, 36,
    31, 31, 32, 31, 9, 9,
    24, 25, 24, 8, 8, 0,
    6, 11, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7800899899879537, 0, 0, 25282767439116344, 30045948798009407, 28282767364012509,
    29172878169905071, 7139551352398793, 33288195153815097, 11768597882173550, 6794415866314396, 33288195751564193,
    5832890014087662, 5832890014087662, 10913637427705176, 6714245517659862, 11768597882173550, 10913637427705176,
    29172862146158415, 6794415866314396, 6714245517659862, 7139551352398793, 23894764947524082, 31266336883968140,
    17069565148207099, 34509636546164092, 17106798054406074, 12134105400401809, 17069565148207099, 16255120801363175,
    17106798054406074, 21071332074381286, 11397139806235602, 26266337600599535, 17069565148207099, 12134105400401809,
    11397139806235602, 12134105400401809, 16078963846209348, 16255120801363175, 23894764947524082, 28315559735212648,
    33098150865828350
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39511143235628147, 44281140818773642, 42511142905185096, 28368397516662330, 33547921743854751, 36547922274039450,
    31368378302461847, 31997885451121588, 32759055762191544, 31997885451121588, 9063395081288510, 9063395081288510,
    24614181135765331, 25375351469443747, 24614181135765331, 8933690662845865, 8933690662845865, 0,
    6714245517766967, 11379919817646542, 10091435386323608
  ]

abbrev PositiveTerm := Fin 43
abbrev NegativeTerm := Fin 21
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
noncomputable def positiveFloor : ℝ := 206295440879 / 500000000000
noncomputable def negativeCeiling : ℝ := 114009453843 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 14114290205096988841447784448, coefficient := (-14114290205096988841447784448) }, { argument := 48137264564290079269272420352, coefficient := (-48137264564290079269272420352) }, { argument := 14114286972280320125898326016, coefficient := (-14114286972280320125898326016) }, { argument := 6392317001276494170590019584, coefficient := (-6392317001276494170590019584) }, { argument := 231659683990679365879152508928, coefficient := (-231659683990679365879152508928) }, { argument := 231659769124709109057946910720, coefficient := (-231659769124709109057946910720) }, { argument := 6392231867246750991795617792, coefficient := (-6392231867246750991795617792) }, { argument := 79112122108523791015401750528, coefficient := (-79112122108523791015401750528) }, { argument := 268168728064310586404763598848, coefficient := (-268168728064310586404763598848) }, { argument := 79112122108523791015401750528, coefficient := (-79112122108523791015401750528) }, { argument := 10348405015901225735484866560, coefficient := (-10348405015901225735484866560) }, { argument := 10348405015901225735484866560, coefficient := (-10348405015901225735484866560) }, { argument := 3789802256695750467803676672, coefficient := (-3789802256695750467803676672) }, { argument := 12846406134817273600228196352, coefficient := (-12846406134817273600228196352) }, { argument := 3789802256695750467803676672, coefficient := (-3789802256695750467803676672) }, { argument := 9458635612664858662901121024, coefficient := (-9458635612664858662901121024) }, { argument := 9458635612664858662901121024, coefficient := (-9458635612664858662901121024) }, { argument := 565372167701790313067529629597696, coefficient := 565372167701790313067529629597696 }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1542130218469336308538824196096, coefficient := 1542130218469336308538824196096 }, { argument := 5234696707339313039028435025920, coefficient := 5234696707339313039028435025920 }, { argument := 1542130138189106099754855563264, coefficient := 1542130138189106099754855563264 }, { argument := 8318957063997755447322114785280, coefficient := (-8318957063997755447322114785280) }, { argument := 2858058255995082109153697595392, coefficient := 2858058255995082109153697595392 }, { argument := 87274772769619309380388257792, coefficient := 87274772769619309380388257792 }, { argument := 99068349197055359888202609459200, coefficient := 99068349197055359888202609459200 }, { argument := 2159586398533345889561522208768, coefficient := 2159586398533345889561522208768 }, { argument := 68705672180338605256901394432, coefficient := 68705672180338605256901394432 }, { argument := 99068390243864828991158806904832, coefficient := 99068390243864828991158806904832 }, { argument := 70562582239266675669250080768, coefficient := 70562582239266675669250080768 }, { argument := 70562582239266675669250080768, coefficient := 70562582239266675669250080768 }, { argument := 1193993167890749275140205314048, coefficient := 1193993167890749275140205314048 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 2159586398533345889561522208768, coefficient := 2159586398533345889561522208768 }, { argument := 1193993167890749275140205314048, coefficient := 1193993167890749275140205314048 }, { argument := 2858026512247584259398571130880, coefficient := 2858026512247584259398571130880 }, { argument := 68705672180338605256901394432, coefficient := 68705672180338605256901394432 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 87274772769619309380388257792, coefficient := 87274772769619309380388257792 }, { argument := 211143053100514459686794627645440, coefficient := (-211143053100514459686794627645440) }, { argument := 589237886929747262312646967296, coefficient := 589237886929747262312646967296 }, { argument := 48789339160844772320854939795456, coefficient := 48789339160844772320854939795456 }, { argument := 5321091830737068770985932488704, coefficient := 5321091830737068770985932488704 }, { argument := 462014301271931051026913395998720, coefficient := 462014301271931051026913395998720 }, { argument := 5460205342651763379377721573376, coefficient := 5460205342651763379377721573376 }, { argument := 173891889893368260489736355840, coefficient := 173891889893368260489736355840 }, { argument := 5321091830737068770985932488704, coefficient := 5321091830737068770985932488704 }, { argument := 3025718884144607732521412591616, coefficient := 3025718884144607732521412591616 }, { argument := 5460205342651763379377721573376, coefficient := 5460205342651763379377721573376 }, { argument := 85241804425729121292068761632768, coefficient := 85241804425729121292068761632768 }, { argument := 3338724285952670601402938032128, coefficient := 3338724285952670601402938032128 }, { argument := 48789363396029562407874176483328, coefficient := 48789363396029562407874176483328 }, { argument := 5321091830737068770985932488704, coefficient := 5321091830737068770985932488704 }, { argument := 173891889893368260489736355840, coefficient := 173891889893368260489736355840 }, { argument := 3338724285952670601402938032128, coefficient := 3338724285952670601402938032128 }, { argument := 173891889893368260489736355840, coefficient := 173891889893368260489736355840 }, { argument := 5355870208715742423083879759872, coefficient := 5355870208715742423083879759872 }, { argument := 3025718884144607732521412591616, coefficient := 3025718884144607732521412591616 }, { argument := 589237886929747262312646967296, coefficient := 589237886929747262312646967296 }, { argument := 691503402424499138516451598532608, coefficient := (-691503402424499138516451598532608) }, { argument := 1577584069582620186079202902016, coefficient := 1577584069582620186079202902016 }, { argument := 43420607903411488771297788297216, coefficient := 43420607903411488771297788297216 }] }

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

end TermShard7


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
