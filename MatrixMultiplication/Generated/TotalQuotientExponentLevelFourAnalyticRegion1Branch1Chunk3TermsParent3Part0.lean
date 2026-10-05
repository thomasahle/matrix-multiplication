import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-500293675976516193498343239843840)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    12583, 3556613, 231, 31708345, 9, 15,
    459, 15, 9, 7353, 471, 1778309,
    459, 15, 471, 15, 459, 15,
    12583, 15795132615, 7340029375, 376741405403, 82837474375, 7340029375,
    188370673325, 7340029375, 7340029375, 304296646375, 1887436125, 82837474375,
    304296646375, 7897575843, 7340029375, 1887436125, 7340029375, 66322750265421,
    67728494115, 1757425995, 514352624776773, 109095598305, 132715296506145, 109095598305,
    113691943215, 67728494115, 3379665375, 363405705, 56889124955, 14222286455,
    1453643685, 34616785881, 124080228627, 8656711365, 31850311985, 363405705,
    31850321471, 363405705, 898239953, 3219646651, 224625245, 14973659925,
    14973670635, 12583, 15795137265, 7340034625
  ]
def negativeCoefficients : Array ℕ := #[
    950744599263179931582988288, 67182520094953829889675886592, 17872759317182677718856105984, 598953702621069201853885972480, 11141460353568422474092118016, 580284393415022003858964480,
    17756702438499673318084313088, 18569100589280704123486863360, 11141460353568422474092118016, 284455409652043786291664388096, 18220929953231690921171484672, 67182614542283487282580160512,
    17756702438499673318084313088, 580284393415022003858964480, 18220929953231690921171484672, 580284393415022003858964480, 17756702438499673318084313088, 18569100589280704123486863360,
    950744599263179931582988288, 36421096119900962845863444480, 16924955421766909259939840000, 868706535929849737429601222656, 191010211188512261647892480000, 16924955421766909259939840000,
    868706400454655417097440460800, 16924955421766909259939840000, 16924955421766909259939840000, 701660294770965295319220224000, 17408525576674535238795264000, 191010211188512261647892480000,
    701660294770965295319220224000, 36421140094632991560220803072, 16924955421766909259939840000, 17408525576674535238795264000, 16924955421766909259939840000, 298691113381536480280304418816,
    78085637339821780802721546240, 4052348444781170261219082240, 1158219144640855715566483144704, 125778661343784784646299975680, 298848279945719755851127848960, 125778661343784784646299975680,
    131077886233114007295586467840, 78085637339821780802721546240, 3896488889212663712710656000, 3351826017530495785123184640, 131177391077771051532455772160, 131177439189185438776180080640,
    3351874128944883028847493120, 79820873725151153709448691712, 286109527761204813063367163904, 79844069535063936591640657920, 36720909615943690952753807360, 3351826017530495785123184640,
    36720920552557083653304221696, 3351826017530495785123184640, 4142400632442974044801728512, 14847999444693263751791509504, 4143604407009306090584145920, 17263454530202247445138636800,
    17263466877991561784469749760, 950744599263179931582988288, 36421106842070955689540321280, 16924967527442707631833088000
  ]
def negativeScales : Array ℕ := #[
    13, 21, 7, 24, 3, 3,
    8, 3, 3, 12, 8, 20,
    8, 3, 8, 3, 8, 3,
    13, 33, 32, 38, 36, 32,
    37, 32, 32, 38, 30, 36,
    38, 32, 32, 30, 32, 45,
    35, 30, 48, 36, 46, 36,
    36, 35, 31, 28, 35, 33,
    30, 35, 36, 33, 34, 28,
    34, 28, 29, 31, 27, 33,
    33, 13, 33, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13619188305682172, 21762072570905099, 7851749043206919, 24918359248975138, 3169925001442313, 3906890600547867,
    8842350344909532, 3906890600547867, 3169925001442313, 12844117271135484, 8879583252627603, 20762074599090391,
    8842350344909532, 3906890600547867, 8879583252627603, 3906890600547867, 8842350344909532, 3906890600547867,
    13619188305682172, 33878761001761125, 32773138691141480, 38454783643775507, 36269564516891146, 32773138691141480,
    37454783418786517, 32773138691141480, 32773138691141480, 38146687477893425, 30813780676122383, 36269564516891146,
    38146687477893425, 32878762743666223, 32773138691141480, 30813780676122383, 32773138691141480, 45914569072807051,
    35979043884784312, 30710816792939441, 48869751098121871, 36666801938015444, 46915327996664589, 36666801938015444,
    36726339065093217, 35979043884784312, 31654233264503624, 28437005827296722, 35727433839274529, 33727434368406004,
    30437026535293032, 35010752727627726, 36852482295338445, 33011171911444570, 34890588456815259, 28437005827296722,
    34890588886494065, 28437005827296722, 29742525652764432, 31584255218471931, 27742944836583051, 33801707843637314,
    33801708875533234, 13619188305682172, 33878761426482556, 32773139723037393
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
noncomputable def negativeCeiling : ℝ := 3595884911 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 950744599263179931582988288, coefficient := (-950744599263179931582988288) }, { argument := 67182520094953829889675886592, coefficient := (-67182520094953829889675886592) }, { argument := 17872759317182677718856105984, coefficient := (-17872759317182677718856105984) }, { argument := 598953702621069201853885972480, coefficient := (-598953702621069201853885972480) }, { argument := 11141460353568422474092118016, coefficient := (-11141460353568422474092118016) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 18569100589280704123486863360, coefficient := (-18569100589280704123486863360) }, { argument := 11141460353568422474092118016, coefficient := (-11141460353568422474092118016) }, { argument := 284455409652043786291664388096, coefficient := (-284455409652043786291664388096) }, { argument := 18220929953231690921171484672, coefficient := (-18220929953231690921171484672) }, { argument := 67182614542283487282580160512, coefficient := (-67182614542283487282580160512) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 18220929953231690921171484672, coefficient := (-18220929953231690921171484672) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 18569100589280704123486863360, coefficient := (-18569100589280704123486863360) }, { argument := 950744599263179931582988288, coefficient := (-950744599263179931582988288) }, { argument := 36421096119900962845863444480, coefficient := (-36421096119900962845863444480) }, { argument := 16924955421766909259939840000, coefficient := (-16924955421766909259939840000) }, { argument := 868706535929849737429601222656, coefficient := (-868706535929849737429601222656) }, { argument := 191010211188512261647892480000, coefficient := (-191010211188512261647892480000) }, { argument := 16924955421766909259939840000, coefficient := (-16924955421766909259939840000) }, { argument := 868706400454655417097440460800, coefficient := (-868706400454655417097440460800) }, { argument := 16924955421766909259939840000, coefficient := (-16924955421766909259939840000) }, { argument := 16924955421766909259939840000, coefficient := (-16924955421766909259939840000) }, { argument := 701660294770965295319220224000, coefficient := (-701660294770965295319220224000) }, { argument := 17408525576674535238795264000, coefficient := (-17408525576674535238795264000) }, { argument := 191010211188512261647892480000, coefficient := (-191010211188512261647892480000) }, { argument := 701660294770965295319220224000, coefficient := (-701660294770965295319220224000) }, { argument := 36421140094632991560220803072, coefficient := (-36421140094632991560220803072) }, { argument := 16924955421766909259939840000, coefficient := (-16924955421766909259939840000) }, { argument := 17408525576674535238795264000, coefficient := (-17408525576674535238795264000) }, { argument := 16924955421766909259939840000, coefficient := (-16924955421766909259939840000) }, { argument := 298691113381536480280304418816, coefficient := (-298691113381536480280304418816) }, { argument := 78085637339821780802721546240, coefficient := (-78085637339821780802721546240) }, { argument := 4052348444781170261219082240, coefficient := (-4052348444781170261219082240) }, { argument := 1158219144640855715566483144704, coefficient := (-1158219144640855715566483144704) }, { argument := 125778661343784784646299975680, coefficient := (-125778661343784784646299975680) }, { argument := 298848279945719755851127848960, coefficient := (-298848279945719755851127848960) }, { argument := 125778661343784784646299975680, coefficient := (-125778661343784784646299975680) }, { argument := 131077886233114007295586467840, coefficient := (-131077886233114007295586467840) }, { argument := 78085637339821780802721546240, coefficient := (-78085637339821780802721546240) }, { argument := 3896488889212663712710656000, coefficient := (-3896488889212663712710656000) }, { argument := 3351826017530495785123184640, coefficient := (-3351826017530495785123184640) }, { argument := 131177391077771051532455772160, coefficient := (-131177391077771051532455772160) }, { argument := 131177439189185438776180080640, coefficient := (-131177439189185438776180080640) }, { argument := 3351874128944883028847493120, coefficient := (-3351874128944883028847493120) }, { argument := 79820873725151153709448691712, coefficient := (-79820873725151153709448691712) }, { argument := 286109527761204813063367163904, coefficient := (-286109527761204813063367163904) }, { argument := 79844069535063936591640657920, coefficient := (-79844069535063936591640657920) }, { argument := 36720909615943690952753807360, coefficient := (-36720909615943690952753807360) }, { argument := 3351826017530495785123184640, coefficient := (-3351826017530495785123184640) }, { argument := 36720920552557083653304221696, coefficient := (-36720920552557083653304221696) }, { argument := 3351826017530495785123184640, coefficient := (-3351826017530495785123184640) }, { argument := 4142400632442974044801728512, coefficient := (-4142400632442974044801728512) }, { argument := 14847999444693263751791509504, coefficient := (-14847999444693263751791509504) }, { argument := 4143604407009306090584145920, coefficient := (-4143604407009306090584145920) }, { argument := 17263454530202247445138636800, coefficient := (-17263454530202247445138636800) }, { argument := 17263466877991561784469749760, coefficient := (-17263466877991561784469749760) }, { argument := 950744599263179931582988288, coefficient := (-950744599263179931582988288) }, { argument := 36421106842070955689540321280, coefficient := (-36421106842070955689540321280) }, { argument := 16924967527442707631833088000, coefficient := (-16924967527442707631833088000) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1238312927356371046915012598693888)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    376741409903, 82837533625, 7340034625, 188370675575, 7340034625, 7340034625,
    304296864025, 1887437475, 82837533625, 304296864025, 987197271, 7340034625,
    1887437475, 7340034625, 515049355429957, 242765664705, 6299308665, 3972018500746621,
    391041699435, 1030617700803065, 391041699435, 407516814405, 242765664705, 12114055125,
    188433617239, 56889124955, 94216809767, 56889124955, 55759972467, 199865757489,
    13944044055, 168988447725, 168988568595, 3556613, 14973659925, 14973670635,
    231, 132716823901985, 16937043975, 439484175, 1029234784138745, 27281825325,
    265573321104325, 27281825325, 28431245475, 16937043975, 845161875, 376867175725,
    14222286455, 376867180315, 14222286455, 31708345, 14973659925, 14973670635,
    9, 15, 363405705, 56889124955, 14222286455, 1453643685,
    55759972467, 199865757489, 13944044055, 14973659925
  ]
def negativeCoefficients : Array ℕ := #[
    868706546306143278891224006656, 191010347809710557559259136000, 16924967527442707631833088000, 868706410830948958559063244800, 16924967527442707631833088000, 16924967527442707631833088000,
    701660796637696250679708876800, 17408538028226784992742604800, 191010347809710557559259136000, 701660796637696250679708876800, 36421150816802984403897679872, 16924967527442707631833088000,
    17408538028226784992742604800, 16924967527442707631833088000, 1159788042595884247907708174336, 279889755418569925822859182080, 14525216848069497148491694080, 4472095259967799630890746773504,
    450840384476618623032030658560, 1160372373324530217533371842560, 450840384476618623032030658560, 469834898816401811610827489280, 279889755418569925822859182080, 13966554661605285719703552000,
    868996678022794313016914477056, 131177391077771051532455772160, 868996688606613725307769716736, 131177391077771051532455772160, 128573742706980002082884419584, 460859059687210147988298006528,
    128611106017558077503900221440, 194830415412282506880850329600, 194830554765904768710444318720, 67182520094953829889675886592, 17263454530202247445138636800, 17263466877991561784469749760,
    17872759317182677718856105984, 298851719335387691473992417280, 78108328892997329274431078400, 4053526050335190740788838400, 1158815347581001217208095866880, 125815212408480727992945868800,
    299008977491245787815660748800, 125815212408480727992945868800, 131115977243534438961669734400, 78108328892997329274431078400, 3897621202245375712296960000, 868996542547599992684753715200,
    131177439189185438776180080640, 868996553131419404975608954880, 131177439189185438776180080640, 598953702621069201853885972480, 17263454530202247445138636800, 17263466877991561784469749760,
    11141460353568422474092118016, 580284393415022003858964480, 3351826017530495785123184640, 131177391077771051532455772160, 131177439189185438776180080640, 3351874128944883028847493120,
    128573742706980002082884419584, 460859059687210147988298006528, 128611106017558077503900221440, 17263454530202247445138636800
  ]
def negativeScales : Array ℕ := #[
    38, 36, 32, 37, 32, 32,
    38, 30, 36, 38, 29, 32,
    30, 32, 48, 37, 32, 51,
    38, 49, 38, 38, 37, 33,
    37, 35, 36, 35, 35, 37,
    33, 37, 37, 21, 33, 33,
    7, 46, 33, 28, 49, 34,
    47, 34, 34, 33, 29, 38,
    33, 38, 33, 24, 33, 33,
    3, 3, 28, 35, 33, 30,
    35, 37, 33, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    38454783661007825, 36269565548787051, 32773139723037393, 37454783436018838, 32773139723037393, 32773139723037393,
    38146688509789330, 30813781708018305, 36269565548787051, 38146688509789330, 29878763168387141, 32773139723037393,
    30813781708018305, 32773139723037393, 48871704018514164, 37820773434776023, 32552546358742394, 51818793766876469,
    38508531503878005, 49872430701977559, 38508531503878005, 38568068630857288, 37820773434776023, 33495962830374827,
    37455265413687854, 35727433839274529, 36455265431258949, 35727433839274529, 35698510797780191, 37540240363605971,
    33698929981597729, 37298133669087917, 37298134700983822, 21762072570905099, 33801707843637314, 33801708875533234,
    7851749043206919, 46915344600281536, 33979463068717082, 28711235976757193, 49870493546356875, 34667221121832627,
    47916103558316659, 34667221121832627, 34726758248911327, 33979463068717082, 29654652448320721, 38455265188773983,
    33727434368406004, 38455265206345082, 33727434368406004, 24918359248975138, 33801707843637314, 33801708875533234,
    3169925001442313, 3906890600547867, 28437005827296722, 35727433839274529, 33727434368406004, 30437026535293032,
    35698510797780191, 37540240363605971, 33698929981597729, 33801707843637314
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
noncomputable def negativeCeiling : ℝ := 2189600589 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 868706546306143278891224006656, coefficient := (-868706546306143278891224006656) }, { argument := 191010347809710557559259136000, coefficient := (-191010347809710557559259136000) }, { argument := 16924967527442707631833088000, coefficient := (-16924967527442707631833088000) }, { argument := 868706410830948958559063244800, coefficient := (-868706410830948958559063244800) }, { argument := 16924967527442707631833088000, coefficient := (-16924967527442707631833088000) }, { argument := 16924967527442707631833088000, coefficient := (-16924967527442707631833088000) }, { argument := 701660796637696250679708876800, coefficient := (-701660796637696250679708876800) }, { argument := 17408538028226784992742604800, coefficient := (-17408538028226784992742604800) }, { argument := 191010347809710557559259136000, coefficient := (-191010347809710557559259136000) }, { argument := 701660796637696250679708876800, coefficient := (-701660796637696250679708876800) }, { argument := 36421150816802984403897679872, coefficient := (-36421150816802984403897679872) }, { argument := 16924967527442707631833088000, coefficient := (-16924967527442707631833088000) }, { argument := 17408538028226784992742604800, coefficient := (-17408538028226784992742604800) }, { argument := 16924967527442707631833088000, coefficient := (-16924967527442707631833088000) }, { argument := 1159788042595884247907708174336, coefficient := (-1159788042595884247907708174336) }, { argument := 279889755418569925822859182080, coefficient := (-279889755418569925822859182080) }, { argument := 14525216848069497148491694080, coefficient := (-14525216848069497148491694080) }, { argument := 4472095259967799630890746773504, coefficient := (-4472095259967799630890746773504) }, { argument := 450840384476618623032030658560, coefficient := (-450840384476618623032030658560) }, { argument := 1160372373324530217533371842560, coefficient := (-1160372373324530217533371842560) }, { argument := 450840384476618623032030658560, coefficient := (-450840384476618623032030658560) }, { argument := 469834898816401811610827489280, coefficient := (-469834898816401811610827489280) }, { argument := 279889755418569925822859182080, coefficient := (-279889755418569925822859182080) }, { argument := 13966554661605285719703552000, coefficient := (-13966554661605285719703552000) }, { argument := 868996678022794313016914477056, coefficient := (-868996678022794313016914477056) }, { argument := 131177391077771051532455772160, coefficient := (-131177391077771051532455772160) }, { argument := 868996688606613725307769716736, coefficient := (-868996688606613725307769716736) }, { argument := 131177391077771051532455772160, coefficient := (-131177391077771051532455772160) }, { argument := 128573742706980002082884419584, coefficient := (-128573742706980002082884419584) }, { argument := 460859059687210147988298006528, coefficient := (-460859059687210147988298006528) }, { argument := 128611106017558077503900221440, coefficient := (-128611106017558077503900221440) }, { argument := 194830415412282506880850329600, coefficient := (-194830415412282506880850329600) }, { argument := 194830554765904768710444318720, coefficient := (-194830554765904768710444318720) }, { argument := 67182520094953829889675886592, coefficient := (-67182520094953829889675886592) }, { argument := 17263454530202247445138636800, coefficient := (-17263454530202247445138636800) }, { argument := 17263466877991561784469749760, coefficient := (-17263466877991561784469749760) }, { argument := 17872759317182677718856105984, coefficient := (-17872759317182677718856105984) }, { argument := 298851719335387691473992417280, coefficient := (-298851719335387691473992417280) }, { argument := 78108328892997329274431078400, coefficient := (-78108328892997329274431078400) }, { argument := 4053526050335190740788838400, coefficient := (-4053526050335190740788838400) }, { argument := 1158815347581001217208095866880, coefficient := (-1158815347581001217208095866880) }, { argument := 125815212408480727992945868800, coefficient := (-125815212408480727992945868800) }, { argument := 299008977491245787815660748800, coefficient := (-299008977491245787815660748800) }, { argument := 125815212408480727992945868800, coefficient := (-125815212408480727992945868800) }, { argument := 131115977243534438961669734400, coefficient := (-131115977243534438961669734400) }, { argument := 78108328892997329274431078400, coefficient := (-78108328892997329274431078400) }, { argument := 3897621202245375712296960000, coefficient := (-3897621202245375712296960000) }, { argument := 868996542547599992684753715200, coefficient := (-868996542547599992684753715200) }, { argument := 131177439189185438776180080640, coefficient := (-131177439189185438776180080640) }, { argument := 868996553131419404975608954880, coefficient := (-868996553131419404975608954880) }, { argument := 131177439189185438776180080640, coefficient := (-131177439189185438776180080640) }, { argument := 598953702621069201853885972480, coefficient := (-598953702621069201853885972480) }, { argument := 17263454530202247445138636800, coefficient := (-17263454530202247445138636800) }, { argument := 17263466877991561784469749760, coefficient := (-17263466877991561784469749760) }, { argument := 11141460353568422474092118016, coefficient := (-11141460353568422474092118016) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 3351826017530495785123184640, coefficient := (-3351826017530495785123184640) }, { argument := 131177391077771051532455772160, coefficient := (-131177391077771051532455772160) }, { argument := 131177439189185438776180080640, coefficient := (-131177439189185438776180080640) }, { argument := 3351874128944883028847493120, coefficient := (-3351874128944883028847493120) }, { argument := 128573742706980002082884419584, coefficient := (-128573742706980002082884419584) }, { argument := 460859059687210147988298006528, coefficient := (-460859059687210147988298006528) }, { argument := 128611106017558077503900221440, coefficient := (-128611106017558077503900221440) }, { argument := 17263454530202247445138636800, coefficient := (-17263454530202247445138636800) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3
