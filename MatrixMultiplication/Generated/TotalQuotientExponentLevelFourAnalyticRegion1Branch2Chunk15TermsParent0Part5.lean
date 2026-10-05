import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
parent chunk 15, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 1556499575136575685388385357135872
def positiveArguments : Array ℕ := #[
    1, 1705, 20405, 30525, 8855, 1705,
    35365, 17765, 1705, 20405, 1705, 47835,
    37205, 5315, 49961, 589965, 41457, 37205,
    589965, 5315, 41457, 41457, 41457, 41457,
    41457, 47835, 49961, 15835, 66507, 288197,
    9501, 9501, 22169, 288197, 288197, 9501,
    3556541, 142515, 66507, 288197, 22169, 142515,
    22169, 288197, 288197, 9501, 763, 14497,
    22127, 228137, 6867, 22127, 6867, 6867,
    588273, 6867, 228137, 588273, 763, 6867
  ]
def positiveCoefficients : Array ℕ := #[
    19807040628566084398385987584, 32979496359087083885984481280, 789380203175568265916144680960, 590439370299784888926496358400, 685122440492002645889484062720, 32979496359087083885984481280,
    684058585770741772215742627840, 687250149934524393236966932480, 32979496359087083885984481280, 789380203175568265916144680960, 32979496359087083885984481280, 925263465300252585153118863360,
    719649361900196455119092449280, 822456413600224520136105656320, 966386285980263811159924146176, 11411582738703115216888465981440, 25660640104327005028246496477184, 719649361900196455119092449280,
    11411582738703115216888465981440, 822456413600224520136105656320, 801895003260218907132703014912, 801895003260218907132703014912, 801895003260218907132703014912, 25660640104327005028246496477184,
    801895003260218907132703014912, 925263465300252585153118863360, 966386285980263811159924146176, 306293445657562447703556751360, 5145729887047049121419753422848, 11149081421935273096409465749504,
    367552134789074937244268101632, 5880834156625198995908289626112, 428810823920587426784979451904, 11149081421935273096409465749504, 11149081421935273096409465749504, 5880834156625198995908289626112,
    137587015789377051508437692710912, 11026564043672248117328043048960, 5145729887047049121419753422848, 11149081421935273096409465749504, 428810823920587426784979451904, 11026564043672248117328043048960,
    428810823920587426784979451904, 11149081421935273096409465749504, 11149081421935273096409465749504, 367552134789074937244268101632, 472274124987372574874015891456, 560825523422504932662893871104,
    427998425769806395979576901632, 4412811355350762496479085985792, 531308390610794146733267877888, 427998425769806395979576901632, 531308390610794146733267877888, 531308390610794146733267877888,
    22757709397829015951741640769536, 531308390610794146733267877888, 4412811355350762496479085985792, 22757709397829015951741640769536, 472274124987372574874015891456, 531308390610794146733267877888
  ]
def positiveScales : Array ℕ := #[
    0, 10, 14, 14, 13, 10,
    15, 14, 10, 14, 10, 15,
    15, 12, 15, 19, 15, 15,
    19, 12, 15, 15, 15, 15,
    15, 15, 15, 13, 16, 18,
    13, 13, 14, 18, 18, 13,
    21, 17, 16, 18, 14, 17,
    14, 18, 18, 13, 9, 13,
    14, 17, 12, 14, 12, 12,
    19, 12, 17, 19, 9, 12
  ]
def negativeArguments : Array ℕ := #[
    1, 55, 1063, 3167
  ]
def negativeCoefficients : Array ℕ := #[
    79228162514264337593543950336, 4357548938284538567644917268480, 84219536752662990861937219207168, 250915590682675157158753690714112
  ]
def negativeScales : Array ℕ := #[
    0, 5, 10, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 10735556023901392, 14316635090145462, 14897703674503048, 13112276591639276, 10735556023901392,
    15110034640852606, 14116750068218584, 10735556023901392, 14316635090145462, 10735556023901392, 15545778977860706,
    15183208898476070, 12375853976418466, 15608514733208297, 19170269842768572, 15339328100393352, 15183208898476070,
    19170269842768572, 12375853976418466, 15339328100393352, 15339328100393352, 15339328100393352, 15339328100393352,
    15339328100393352, 15545778977860706, 15608514733208297, 13950829246263005, 16021218574806950, 18136695792226886,
    13213863652749345, 13213863652749345, 14436256074085791, 18136695792226886, 18136695792226886, 13213863652749345,
    21762043364410688, 17120754248357864, 16021218574806950, 18136695792226886, 14436256074085791, 17120754248357864,
    14436256074085791, 18136695792226886, 18136695792226886, 13213863652749345, 9575539246834353, 13823466760214044,
    14433520241962100, 17799540920992980, 12745464248264213, 14433520241962100, 12745464248264213, 12745464248264213,
    19166126296749564, 12745464248264213, 17799540920992980, 19166126296749564, 9575539246834353, 12745464248264213
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 5781359713964302, 10053925881531105, 11628901152040529
  ]

abbrev PositiveTerm := Fin 60
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 89883685143 / 1000000000000
noncomputable def negativeCeiling : ℝ := 22809041951 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 32979496359087083885984481280, coefficient := 32979496359087083885984481280 }, { argument := 789380203175568265916144680960, coefficient := 789380203175568265916144680960 }, { argument := 590439370299784888926496358400, coefficient := 590439370299784888926496358400 }, { argument := 685122440492002645889484062720, coefficient := 685122440492002645889484062720 }, { argument := 32979496359087083885984481280, coefficient := 32979496359087083885984481280 }, { argument := 684058585770741772215742627840, coefficient := 684058585770741772215742627840 }, { argument := 687250149934524393236966932480, coefficient := 687250149934524393236966932480 }, { argument := 32979496359087083885984481280, coefficient := 32979496359087083885984481280 }, { argument := 789380203175568265916144680960, coefficient := 789380203175568265916144680960 }, { argument := 32979496359087083885984481280, coefficient := 32979496359087083885984481280 }, { argument := 4357548938284538567644917268480, coefficient := (-4357548938284538567644917268480) }, { argument := 925263465300252585153118863360, coefficient := 925263465300252585153118863360 }, { argument := 719649361900196455119092449280, coefficient := 719649361900196455119092449280 }, { argument := 822456413600224520136105656320, coefficient := 822456413600224520136105656320 }, { argument := 966386285980263811159924146176, coefficient := 966386285980263811159924146176 }, { argument := 11411582738703115216888465981440, coefficient := 11411582738703115216888465981440 }, { argument := 25660640104327005028246496477184, coefficient := 25660640104327005028246496477184 }, { argument := 719649361900196455119092449280, coefficient := 719649361900196455119092449280 }, { argument := 11411582738703115216888465981440, coefficient := 11411582738703115216888465981440 }, { argument := 822456413600224520136105656320, coefficient := 822456413600224520136105656320 }, { argument := 801895003260218907132703014912, coefficient := 801895003260218907132703014912 }, { argument := 801895003260218907132703014912, coefficient := 801895003260218907132703014912 }, { argument := 801895003260218907132703014912, coefficient := 801895003260218907132703014912 }, { argument := 25660640104327005028246496477184, coefficient := 25660640104327005028246496477184 }, { argument := 801895003260218907132703014912, coefficient := 801895003260218907132703014912 }, { argument := 925263465300252585153118863360, coefficient := 925263465300252585153118863360 }, { argument := 966386285980263811159924146176, coefficient := 966386285980263811159924146176 }, { argument := 84219536752662990861937219207168, coefficient := (-84219536752662990861937219207168) }, { argument := 306293445657562447703556751360, coefficient := 306293445657562447703556751360 }, { argument := 5145729887047049121419753422848, coefficient := 5145729887047049121419753422848 }, { argument := 11149081421935273096409465749504, coefficient := 11149081421935273096409465749504 }, { argument := 367552134789074937244268101632, coefficient := 367552134789074937244268101632 }, { argument := 5880834156625198995908289626112, coefficient := 5880834156625198995908289626112 }, { argument := 428810823920587426784979451904, coefficient := 428810823920587426784979451904 }, { argument := 11149081421935273096409465749504, coefficient := 11149081421935273096409465749504 }, { argument := 11149081421935273096409465749504, coefficient := 11149081421935273096409465749504 }, { argument := 5880834156625198995908289626112, coefficient := 5880834156625198995908289626112 }, { argument := 137587015789377051508437692710912, coefficient := 137587015789377051508437692710912 }, { argument := 11026564043672248117328043048960, coefficient := 11026564043672248117328043048960 }, { argument := 5145729887047049121419753422848, coefficient := 5145729887047049121419753422848 }, { argument := 11149081421935273096409465749504, coefficient := 11149081421935273096409465749504 }, { argument := 428810823920587426784979451904, coefficient := 428810823920587426784979451904 }, { argument := 11026564043672248117328043048960, coefficient := 11026564043672248117328043048960 }, { argument := 428810823920587426784979451904, coefficient := 428810823920587426784979451904 }, { argument := 11149081421935273096409465749504, coefficient := 11149081421935273096409465749504 }, { argument := 11149081421935273096409465749504, coefficient := 11149081421935273096409465749504 }, { argument := 367552134789074937244268101632, coefficient := 367552134789074937244268101632 }, { argument := 250915590682675157158753690714112, coefficient := (-250915590682675157158753690714112) }, { argument := 472274124987372574874015891456, coefficient := 472274124987372574874015891456 }, { argument := 560825523422504932662893871104, coefficient := 560825523422504932662893871104 }, { argument := 427998425769806395979576901632, coefficient := 427998425769806395979576901632 }, { argument := 4412811355350762496479085985792, coefficient := 4412811355350762496479085985792 }, { argument := 531308390610794146733267877888, coefficient := 531308390610794146733267877888 }, { argument := 427998425769806395979576901632, coefficient := 427998425769806395979576901632 }, { argument := 531308390610794146733267877888, coefficient := 531308390610794146733267877888 }, { argument := 531308390610794146733267877888, coefficient := 531308390610794146733267877888 }, { argument := 22757709397829015951741640769536, coefficient := 22757709397829015951741640769536 }, { argument := 531308390610794146733267877888, coefficient := 531308390610794146733267877888 }, { argument := 4412811355350762496479085985792, coefficient := 4412811355350762496479085985792 }, { argument := 22757709397829015951741640769536, coefficient := 22757709397829015951741640769536 }, { argument := 472274124987372574874015891456, coefficient := 472274124987372574874015891456 }, { argument := 531308390610794146733267877888, coefficient := 531308390610794146733267877888 }] }

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

end TermShard10


end Parent0

namespace Parent0

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-103373191124401637291317969882710016)
def positiveArguments : Array ℕ := #[
    6867, 14497, 45, 801, 45, 1425,
    2433, 45, 2433, 2433, 801, 45,
    1, 314572855, 314572745, 9454323223, 16835574375, 9454322971,
    626507151, 23276831345, 186207507435, 5019200533, 184558315, 28059215339,
    285633452149, 14029608051, 184546767, 102568677, 8584707355, 105,
    93, 4353, 1185, 4292352957, 4353, 105,
    105, 45, 105, 1185, 45, 51285059,
    93, 13023331, 501, 64298909, 807, 25,
    807, 539, 13027427, 501, 3
  ]
def positiveCoefficients : Array ℕ := #[
    531308390610794146733267877888, 560825523422504932662893871104, 3481706360490132023153786880, 61974373216724350012137406464, 3481706360490132023153786880, 55127017374427090366601625600,
    94122128611916569025924038656, 3481706360490132023153786880, 94122128611916569025924038656, 94122128611916569025924038656, 61974373216724350012137406464, 3481706360490132023153786880,
    79228162514264337593543950336, 2971056613745225775418871644160, 2971055574824599544096924631040, 44646779106511318425616890462208, 159007504296718150850083553280000, 44646777916474964742466296610816,
    23668770969284413817707737120768, 879373825368300506073506208808960, 879340091969744261265110083829760, 23702504367840658626103862099968, 871552000890898085287548682240, 132505898052515429717626736082944,
    1348865840814788234350843295432704, 132505901655681056147166034132992, 871497467002753906624620920832, 968733764914165346056362000384, 81080268556993049544513195868160, 4061990753905154027012751360,
    3597763239173136423925579776, 168398530969039385519871492096, 45842467079786738304858193920, 81080254947132845914195689996288, 168398530969039385519871492096, 4061990753905154027012751360,
    4061990753905154027012751360, 3481706360490132023153786880, 4061990753905154027012751360, 45842467079786738304858193920, 3481706360490132023153786880, 968747374774368976373867872256,
    3597763239173136423925579776, 123001883619434438941057482752, 19381498740061734928889413632, 1214572050986741505830898630656, 31219300365728183807612289024, 967140655691703339764940800,
    31219300365728183807612289024, 20851552536713124005332123648, 123040569245662107074648080384, 19381498740061734928889413632, 928455029464035206174343168
  ]
def positiveScales : Array ℕ := #[
    12, 13, 5, 9, 5, 10,
    11, 5, 11, 11, 9, 5,
    0, 28, 28, 33, 33, 33,
    29, 34, 37, 32, 27, 34,
    38, 33, 27, 26, 32, 6,
    6, 12, 10, 31, 12, 6,
    6, 5, 6, 10, 5, 25,
    6, 23, 8, 25, 9, 4,
    9, 9, 23, 8, 1
  ]
def negativeArguments : Array ℕ := #[
    763, 3, 1, 75, 1567, 5699,
    2549, 2077, 5
  ]
def negativeCoefficients : Array ℕ := #[
    60451087998383689583874034106368, 475368975085586025561263702016, 79228162514264337593543950336, 5942112188569825319515796275200, 248301061319704434018166740353024, 1806085192675169839782427891859456,
    1615620689990878372207548235251712, 164556893542127029181790784847872, 1584563250285286751870879006720
  ]
def negativeScales : Array ℕ := #[
    9, 1, 0, 6, 10, 12,
    11, 11, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12745464248264213, 13823466760214044, 5491853096329661, 9645658432407524, 5491853096329661, 10476746203939458,
    11248520604938428, 5491853096329661, 11248520604938428, 11248520604938428, 9645658432407524, 5491853096329661,
    0, 28228818942737079, 28228818438254637, 33138327042170025, 33970793890027992, 33138327003715749,
    29222755735770311, 34438175627652840, 37438120283794654, 32224810441483398, 27459501496622972, 34707755614192348,
    38055373995198324, 33707755653422822, 27459411222914210, 26612014978969487, 32999121807428251, 6714245517659862,
    6539158811107971, 12087794304787900, 10210671343785621, 31999121565262316, 12087794304787900, 6714245517659862,
    6714245517659862, 5491853096329661, 6714245517659862, 10210671343785621, 5491853096329661, 25612035247427766,
    6539158811107971, 23634595160529729, 8968666792316714, 25938290922331468, 9656424863276222, 4643856189773592,
    9656424863276222, 9074141462752505, 23635048834771072, 8968666792316714, 1584962500720924
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    9575539246837362, 1584962500724866, 0, 6228818690495881, 10613789464480826, 12476493077341713,
    11315715658022203, 11020285500844648, 2321928094887363
  ]

abbrev PositiveTerm := Fin 53
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
noncomputable def positiveFloor : ℝ := 1673362694393 / 1000000000000
noncomputable def negativeCeiling : ℝ := 276158430691 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 531308390610794146733267877888, coefficient := 531308390610794146733267877888 }, { argument := 560825523422504932662893871104, coefficient := 560825523422504932662893871104 }, { argument := 60451087998383689583874034106368, coefficient := (-60451087998383689583874034106368) }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 61974373216724350012137406464, coefficient := 61974373216724350012137406464 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 55127017374427090366601625600, coefficient := 55127017374427090366601625600 }, { argument := 94122128611916569025924038656, coefficient := 94122128611916569025924038656 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 94122128611916569025924038656, coefficient := 94122128611916569025924038656 }, { argument := 94122128611916569025924038656, coefficient := 94122128611916569025924038656 }, { argument := 61974373216724350012137406464, coefficient := 61974373216724350012137406464 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 2971056613745225775418871644160, coefficient := 2971056613745225775418871644160 }, { argument := 2971055574824599544096924631040, coefficient := 2971055574824599544096924631040 }, { argument := 5942112188569825319515796275200, coefficient := (-5942112188569825319515796275200) }, { argument := 44646779106511318425616890462208, coefficient := 44646779106511318425616890462208 }, { argument := 159007504296718150850083553280000, coefficient := 159007504296718150850083553280000 }, { argument := 44646777916474964742466296610816, coefficient := 44646777916474964742466296610816 }, { argument := 248301061319704434018166740353024, coefficient := (-248301061319704434018166740353024) }, { argument := 23668770969284413817707737120768, coefficient := 23668770969284413817707737120768 }, { argument := 879373825368300506073506208808960, coefficient := 879373825368300506073506208808960 }, { argument := 879340091969744261265110083829760, coefficient := 879340091969744261265110083829760 }, { argument := 23702504367840658626103862099968, coefficient := 23702504367840658626103862099968 }, { argument := 1806085192675169839782427891859456, coefficient := (-1806085192675169839782427891859456) }, { argument := 871552000890898085287548682240, coefficient := 871552000890898085287548682240 }, { argument := 132505898052515429717626736082944, coefficient := 132505898052515429717626736082944 }, { argument := 1348865840814788234350843295432704, coefficient := 1348865840814788234350843295432704 }, { argument := 132505901655681056147166034132992, coefficient := 132505901655681056147166034132992 }, { argument := 871497467002753906624620920832, coefficient := 871497467002753906624620920832 }, { argument := 1615620689990878372207548235251712, coefficient := (-1615620689990878372207548235251712) }, { argument := 968733764914165346056362000384, coefficient := 968733764914165346056362000384 }, { argument := 81080268556993049544513195868160, coefficient := 81080268556993049544513195868160 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 81080254947132845914195689996288, coefficient := 81080254947132845914195689996288 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 968747374774368976373867872256, coefficient := 968747374774368976373867872256 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 164556893542127029181790784847872, coefficient := (-164556893542127029181790784847872) }, { argument := 123001883619434438941057482752, coefficient := 123001883619434438941057482752 }, { argument := 19381498740061734928889413632, coefficient := 19381498740061734928889413632 }, { argument := 1214572050986741505830898630656, coefficient := 1214572050986741505830898630656 }, { argument := 31219300365728183807612289024, coefficient := 31219300365728183807612289024 }, { argument := 967140655691703339764940800, coefficient := 967140655691703339764940800 }, { argument := 31219300365728183807612289024, coefficient := 31219300365728183807612289024 }, { argument := 20851552536713124005332123648, coefficient := 20851552536713124005332123648 }, { argument := 123040569245662107074648080384, coefficient := 123040569245662107074648080384 }, { argument := 19381498740061734928889413632, coefficient := 19381498740061734928889413632 }, { argument := 928455029464035206174343168, coefficient := 928455029464035206174343168 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }] }

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

end TermShard11


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
