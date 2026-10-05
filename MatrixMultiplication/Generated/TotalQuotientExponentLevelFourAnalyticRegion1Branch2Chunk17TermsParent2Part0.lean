import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 17, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-19871818180657203146106719969476608)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    15744679, 513290585, 2115, 2475, 30311, 65291,
    256645249, 30311, 2115, 2063, 1029, 2063,
    65291, 1029, 7872383, 2475, 18918081516391, 2248653123162899,
    84498603, 87953997987368921, 44607543, 3249519, 84498603, 84466725,
    44607543, 1043040345, 2610729, 2248653143610131, 84498603, 3249519,
    2610729, 3249519, 42249543, 84466725, 79559636371955, 675633194020339,
    8058292065, 24650560237570573, 126812069865, 3817085715, 394391463884632447, 3817085715,
    3817085715, 326997009585, 3817085715, 126812069865, 326997009585, 10827631028194945,
    3817085715, 3817085715, 8058292065, 1623, 2705, 82773,
    2705, 84937, 2705, 82773, 47067, 84937,
    1325991, 1623, 2705, 82773
  ]
def negativeCoefficients : Array ℕ := #[
    74352144393141562733529923584, 2423946254576552670480469852160, 40910049735759051272056995840, 47873462456739315318364569600, 586300008293424398632302411776, 1262911611015340055131854995456,
    2423945843730668660821336260608, 586300008293424398632302411776, 40910049735759051272056995840, 39904223453839679798701457408, 39807509388270509464724963328, 39904223453839679798701457408,
    1262911611015340055131854995456, 39807509388270509464724963328, 74352555239025572392663515136, 47873462456739315318364569600, 85199464867783175515653799936, 10127033367561933984158034427904,
    798066741313016903325896933376, 99027398140415006941330175688704, 421306331892732924529377017856, 30690839222096173290328424448, 798066741313016903325896933376, 797765662115535066225652531200,
    421306331892732924529377017856, 9851237531017582667442149130240, 789044424029170302662870040576, 10127033459648080400116116094976, 798066741313016903325896933376, 30690839222096173290328424448,
    789044424029170302662870040576, 30690839222096173290328424448, 798071303119039355403173363712, 797765662115535066225652531200, 89576187179617174574512209920, 3042781400829136746665312518144,
    74324625697129727450960363520, 111016253900396797914755218014208, 584817449564257592311503912960, 70412803292017636532488765440, 111011328111808444946543628255232, 70412803292017636532488765440,
    70412803292017636532488765440, 3016015074341422098141602119680, 70412803292017636532488765440, 584817449564257592311503912960, 3016015074341422098141602119680, 3047707191492748423169226833920,
    70412803292017636532488765440, 70412803292017636532488765440, 74324625697129727450960363520, 30657603206789736727314432, 817536085514392979395051520, 781768881773138286546518016,
    25548002672324780606095360, 802207283910998111031394304, 25548002672324780606095360, 781768881773138286546518016, 444535246498451182546059264, 802207283910998111031394304,
    12523630909973607453107945472, 490521651308635787637030912, 817536085514392979395051520, 781768881773138286546518016
  ]
def negativeScales : Array ℕ := #[
    23, 28, 11, 11, 14, 15,
    27, 14, 11, 11, 10, 11,
    15, 10, 22, 11, 44, 50,
    26, 56, 25, 21, 26, 26,
    25, 29, 21, 50, 26, 21,
    21, 21, 25, 26, 46, 49,
    32, 54, 36, 31, 58, 31,
    31, 38, 31, 36, 38, 53,
    31, 31, 32, 10, 11, 16,
    11, 16, 11, 16, 15, 16,
    20, 10, 11, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23908361013618743, 28935200565449087, 11046441948007313, 11273212809854335, 14887553832363463, 15994596539282001,
    27935200320919964, 14887553832363463, 11046441948007313, 11010528105886485, 10007027266893969, 11010528105886485,
    15994596539282001, 10007027266893969, 22908368985463267, 11273212809854335, 44104831025853363, 50997982574631317,
    26332424153989406, 56287598675718321, 25410784350333898, 21631794752810574, 26332424153989406, 26331879779192476,
    25410784350333898, 29958147828597039, 21316021279503764, 50997982587749895, 26332424153989406, 21631794752810574,
    21316021279503764, 21631794752810574, 25332432400512881, 26331879779192476, 46177101915871570, 49263233538255853,
    32907826954528630, 54452469953554791, 36883901113524165, 31829824438677684, 58452405939789424, 31829824438677684,
    31829824438677684, 38250486485977868, 31829824438677684, 36883901113524165, 38250486485977868, 53265567149165578,
    31829824438677684, 31829824438677684, 32907826954528630, 10664447284578613, 11401412878714185, 16336872626519468,
    11401412878714185, 16374105532718445, 11401412878714185, 16336872626519468, 15522428279676108, 16374105532718445,
    20338639552693656, 10664447284578613, 11401412878714185, 16336872626519468
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
noncomputable def negativeCeiling : ℝ := 122982041497 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 74352144393141562733529923584, coefficient := (-74352144393141562733529923584) }, { argument := 2423946254576552670480469852160, coefficient := (-2423946254576552670480469852160) }, { argument := 40910049735759051272056995840, coefficient := (-40910049735759051272056995840) }, { argument := 47873462456739315318364569600, coefficient := (-47873462456739315318364569600) }, { argument := 586300008293424398632302411776, coefficient := (-586300008293424398632302411776) }, { argument := 1262911611015340055131854995456, coefficient := (-1262911611015340055131854995456) }, { argument := 2423945843730668660821336260608, coefficient := (-2423945843730668660821336260608) }, { argument := 586300008293424398632302411776, coefficient := (-586300008293424398632302411776) }, { argument := 40910049735759051272056995840, coefficient := (-40910049735759051272056995840) }, { argument := 39904223453839679798701457408, coefficient := (-39904223453839679798701457408) }, { argument := 39807509388270509464724963328, coefficient := (-39807509388270509464724963328) }, { argument := 39904223453839679798701457408, coefficient := (-39904223453839679798701457408) }, { argument := 1262911611015340055131854995456, coefficient := (-1262911611015340055131854995456) }, { argument := 39807509388270509464724963328, coefficient := (-39807509388270509464724963328) }, { argument := 74352555239025572392663515136, coefficient := (-74352555239025572392663515136) }, { argument := 47873462456739315318364569600, coefficient := (-47873462456739315318364569600) }, { argument := 85199464867783175515653799936, coefficient := (-85199464867783175515653799936) }, { argument := 10127033367561933984158034427904, coefficient := (-10127033367561933984158034427904) }, { argument := 798066741313016903325896933376, coefficient := (-798066741313016903325896933376) }, { argument := 99027398140415006941330175688704, coefficient := (-99027398140415006941330175688704) }, { argument := 421306331892732924529377017856, coefficient := (-421306331892732924529377017856) }, { argument := 30690839222096173290328424448, coefficient := (-30690839222096173290328424448) }, { argument := 798066741313016903325896933376, coefficient := (-798066741313016903325896933376) }, { argument := 797765662115535066225652531200, coefficient := (-797765662115535066225652531200) }, { argument := 421306331892732924529377017856, coefficient := (-421306331892732924529377017856) }, { argument := 9851237531017582667442149130240, coefficient := (-9851237531017582667442149130240) }, { argument := 789044424029170302662870040576, coefficient := (-789044424029170302662870040576) }, { argument := 10127033459648080400116116094976, coefficient := (-10127033459648080400116116094976) }, { argument := 798066741313016903325896933376, coefficient := (-798066741313016903325896933376) }, { argument := 30690839222096173290328424448, coefficient := (-30690839222096173290328424448) }, { argument := 789044424029170302662870040576, coefficient := (-789044424029170302662870040576) }, { argument := 30690839222096173290328424448, coefficient := (-30690839222096173290328424448) }, { argument := 798071303119039355403173363712, coefficient := (-798071303119039355403173363712) }, { argument := 797765662115535066225652531200, coefficient := (-797765662115535066225652531200) }, { argument := 89576187179617174574512209920, coefficient := (-89576187179617174574512209920) }, { argument := 3042781400829136746665312518144, coefficient := (-3042781400829136746665312518144) }, { argument := 74324625697129727450960363520, coefficient := (-74324625697129727450960363520) }, { argument := 111016253900396797914755218014208, coefficient := (-111016253900396797914755218014208) }, { argument := 584817449564257592311503912960, coefficient := (-584817449564257592311503912960) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 111011328111808444946543628255232, coefficient := (-111011328111808444946543628255232) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 3016015074341422098141602119680, coefficient := (-3016015074341422098141602119680) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 584817449564257592311503912960, coefficient := (-584817449564257592311503912960) }, { argument := 3016015074341422098141602119680, coefficient := (-3016015074341422098141602119680) }, { argument := 3047707191492748423169226833920, coefficient := (-3047707191492748423169226833920) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 70412803292017636532488765440, coefficient := (-70412803292017636532488765440) }, { argument := 74324625697129727450960363520, coefficient := (-74324625697129727450960363520) }, { argument := 30657603206789736727314432, coefficient := (-30657603206789736727314432) }, { argument := 817536085514392979395051520, coefficient := (-817536085514392979395051520) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 802207283910998111031394304, coefficient := (-802207283910998111031394304) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }, { argument := 444535246498451182546059264, coefficient := (-444535246498451182546059264) }, { argument := 802207283910998111031394304, coefficient := (-802207283910998111031394304) }, { argument := 12523630909973607453107945472, coefficient := (-12523630909973607453107945472) }, { argument := 490521651308635787637030912, coefficient := (-490521651308635787637030912) }, { argument := 817536085514392979395051520, coefficient := (-817536085514392979395051520) }, { argument := 781768881773138286546518016, coefficient := (-781768881773138286546518016) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-50129149147646768368566009914720256)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2705, 1623, 2705, 41657, 47067, 1623,
    933297165, 16331536935, 16331544945, 933289155, 2707045365322337, 1928814141,
    108360345, 4823398995440851, 5858682653, 2707045274994681, 5858682653, 5858682653,
    1928814141, 108360345, 52432425, 917502075, 917502525, 52431975,
    8117435493, 13757957019, 8117435493, 37863440682273, 1623, 37863432483551,
    1623, 18918077410457, 2248652467662061, 84498603, 87953971823718439, 44607543,
    3249519, 84498603, 84466725, 44607543, 1043040345, 2610729,
    2248652488109293, 84498603, 3249519, 2610729, 3249519, 42249543,
    84466725, 79559619950093, 4815548735745917, 13657716895, 175902676562005123, 214929334295,
    6469444845, 1407157767041439089, 6469444845, 6469444845, 554215775055, 6469444845,
    214929334295, 554215775055, 38588035457305231, 6469444845
  ]
def negativeCoefficients : Array ℕ := #[
    25548002672324780606095360, 490521651308635787637030912, 25548002672324780606095360, 786878482307603242667737088, 444535246498451182546059264, 30657603206789736727314432,
    4304073486868418889158492160, 150631841085139952339496468480, 150631914964349967546250690560, 4304036547263411285781381120, 3047862124635176281909690892288, 4447542603097366185463775232,
    249861943994234055363133440, 10861328959263320649188715266048, 6754601219310793963316707328, 3047862022935276806197104082944, 6754601219310793963316707328, 6754601219310793963316707328,
    4447542603097366185463775232, 249861943994234055363133440, 241801881284742634222387200, 8462462982311233277499801600, 8462467132828649862148915200, 241799806026034341897830400,
    74870127537108661230416953344, 253789512106588979022689992704, 74870127537108661230416953344, 85260888673824780815595208704, 30657603206789736727314432, 85260870211944108758451355648,
    30657603206789736727314432, 85199446376300343107803676672, 10127030415448604226310169952256, 798066741313016903325896933376, 99027368682763366594555659943936, 421306331892732924529377017856,
    30690839222096173290328424448, 798066741313016903325896933376, 797765662115535066225652531200, 421306331892732924529377017856, 9851237531017582667442149130240, 789044424029170302662870040576,
    10127030507534750642268251619328, 798066741313016903325896933376, 30690839222096173290328424448, 789044424029170302662870040576, 30690839222096173290328424448, 798071303119039355403173363712,
    797765662115535066225652531200, 89576168690244278592085164032, 10843651745944887456185939132416, 251940408193244068428717752320, 396097614309059576185202885525504, 1982373211836315170004910735360,
    238680386709389117458785239040, 396079699706207768676337801232384, 238680386709389117458785239040, 238680386709389117458785239040, 10223476564052167197817967738880, 238680386709389117458785239040,
    1982373211836315170004910735360, 10223476564052167197817967738880, 10861566381654957846346162241536, 238680386709389117458785239040
  ]
def negativeScales : Array ℕ := #[
    11, 10, 11, 15, 15, 10,
    29, 33, 33, 29, 51, 30,
    26, 52, 32, 51, 32, 32,
    30, 26, 25, 29, 29, 25,
    32, 33, 32, 45, 10, 45,
    10, 44, 50, 26, 56, 25,
    21, 26, 26, 25, 29, 21,
    50, 26, 21, 21, 21, 25,
    26, 46, 52, 33, 57, 37,
    32, 60, 32, 32, 39, 32,
    37, 39, 55, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11401412878714185, 10664447284578613, 11401412878714185, 15346271324521718, 15522428279676108, 10664447284578613,
    29797761272960163, 33926941522925424, 33926942230512585, 29797748891012112, 51265640488099057, 30845066988697348,
    26691261651101173, 52098971579239595, 32447929159651114, 51265640439959759, 32447929159651114, 32447929159651114,
    30845066988697348, 26691261651101173, 25643955936282215, 29773136180191675, 29773136887778755, 25643943554334315,
    32918376874897093, 33679547202578477, 32918376874897093, 45105870749429703, 10664447284578613, 45105870437037151,
    10664447284578613, 44104830712734337, 50997982154073659, 26332424153989406, 56287598246560178, 25410784350333898,
    21631794752810574, 26332424153989406, 26331879779192476, 25410784350333898, 29958147828597039, 21316021279503764,
    50997982167192240, 26332424153989406, 21631794752810574, 21316021279503764, 21631794752810574, 25332432400512881,
    26331879779192476, 46177101618085627, 52096621627034958, 33668997283227462, 57287555048330242, 37645071443966470,
    32590994771196291, 60287489797007739, 32590994771196291, 32590994771196291, 39011656819664614, 32590994771196291,
    37645071443966470, 39011656819664614, 55099003115377081, 32590994771196291
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
noncomputable def negativeCeiling : ℝ := 682881273739 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 490521651308635787637030912, coefficient := (-490521651308635787637030912) }, { argument := 25548002672324780606095360, coefficient := (-25548002672324780606095360) }, { argument := 786878482307603242667737088, coefficient := (-786878482307603242667737088) }, { argument := 444535246498451182546059264, coefficient := (-444535246498451182546059264) }, { argument := 30657603206789736727314432, coefficient := (-30657603206789736727314432) }, { argument := 4304073486868418889158492160, coefficient := (-4304073486868418889158492160) }, { argument := 150631841085139952339496468480, coefficient := (-150631841085139952339496468480) }, { argument := 150631914964349967546250690560, coefficient := (-150631914964349967546250690560) }, { argument := 4304036547263411285781381120, coefficient := (-4304036547263411285781381120) }, { argument := 3047862124635176281909690892288, coefficient := (-3047862124635176281909690892288) }, { argument := 4447542603097366185463775232, coefficient := (-4447542603097366185463775232) }, { argument := 249861943994234055363133440, coefficient := (-249861943994234055363133440) }, { argument := 10861328959263320649188715266048, coefficient := (-10861328959263320649188715266048) }, { argument := 6754601219310793963316707328, coefficient := (-6754601219310793963316707328) }, { argument := 3047862022935276806197104082944, coefficient := (-3047862022935276806197104082944) }, { argument := 6754601219310793963316707328, coefficient := (-6754601219310793963316707328) }, { argument := 6754601219310793963316707328, coefficient := (-6754601219310793963316707328) }, { argument := 4447542603097366185463775232, coefficient := (-4447542603097366185463775232) }, { argument := 249861943994234055363133440, coefficient := (-249861943994234055363133440) }, { argument := 241801881284742634222387200, coefficient := (-241801881284742634222387200) }, { argument := 8462462982311233277499801600, coefficient := (-8462462982311233277499801600) }, { argument := 8462467132828649862148915200, coefficient := (-8462467132828649862148915200) }, { argument := 241799806026034341897830400, coefficient := (-241799806026034341897830400) }, { argument := 74870127537108661230416953344, coefficient := (-74870127537108661230416953344) }, { argument := 253789512106588979022689992704, coefficient := (-253789512106588979022689992704) }, { argument := 74870127537108661230416953344, coefficient := (-74870127537108661230416953344) }, { argument := 85260888673824780815595208704, coefficient := (-85260888673824780815595208704) }, { argument := 30657603206789736727314432, coefficient := (-30657603206789736727314432) }, { argument := 85260870211944108758451355648, coefficient := (-85260870211944108758451355648) }, { argument := 30657603206789736727314432, coefficient := (-30657603206789736727314432) }, { argument := 85199446376300343107803676672, coefficient := (-85199446376300343107803676672) }, { argument := 10127030415448604226310169952256, coefficient := (-10127030415448604226310169952256) }, { argument := 798066741313016903325896933376, coefficient := (-798066741313016903325896933376) }, { argument := 99027368682763366594555659943936, coefficient := (-99027368682763366594555659943936) }, { argument := 421306331892732924529377017856, coefficient := (-421306331892732924529377017856) }, { argument := 30690839222096173290328424448, coefficient := (-30690839222096173290328424448) }, { argument := 798066741313016903325896933376, coefficient := (-798066741313016903325896933376) }, { argument := 797765662115535066225652531200, coefficient := (-797765662115535066225652531200) }, { argument := 421306331892732924529377017856, coefficient := (-421306331892732924529377017856) }, { argument := 9851237531017582667442149130240, coefficient := (-9851237531017582667442149130240) }, { argument := 789044424029170302662870040576, coefficient := (-789044424029170302662870040576) }, { argument := 10127030507534750642268251619328, coefficient := (-10127030507534750642268251619328) }, { argument := 798066741313016903325896933376, coefficient := (-798066741313016903325896933376) }, { argument := 30690839222096173290328424448, coefficient := (-30690839222096173290328424448) }, { argument := 789044424029170302662870040576, coefficient := (-789044424029170302662870040576) }, { argument := 30690839222096173290328424448, coefficient := (-30690839222096173290328424448) }, { argument := 798071303119039355403173363712, coefficient := (-798071303119039355403173363712) }, { argument := 797765662115535066225652531200, coefficient := (-797765662115535066225652531200) }, { argument := 89576168690244278592085164032, coefficient := (-89576168690244278592085164032) }, { argument := 10843651745944887456185939132416, coefficient := (-10843651745944887456185939132416) }, { argument := 251940408193244068428717752320, coefficient := (-251940408193244068428717752320) }, { argument := 396097614309059576185202885525504, coefficient := (-396097614309059576185202885525504) }, { argument := 1982373211836315170004910735360, coefficient := (-1982373211836315170004910735360) }, { argument := 238680386709389117458785239040, coefficient := (-238680386709389117458785239040) }, { argument := 396079699706207768676337801232384, coefficient := (-396079699706207768676337801232384) }, { argument := 238680386709389117458785239040, coefficient := (-238680386709389117458785239040) }, { argument := 238680386709389117458785239040, coefficient := (-238680386709389117458785239040) }, { argument := 10223476564052167197817967738880, coefficient := (-10223476564052167197817967738880) }, { argument := 238680386709389117458785239040, coefficient := (-238680386709389117458785239040) }, { argument := 1982373211836315170004910735360, coefficient := (-1982373211836315170004910735360) }, { argument := 10223476564052167197817967738880, coefficient := (-10223476564052167197817967738880) }, { argument := 10861566381654957846346162241536, coefficient := (-10861566381654957846346162241536) }, { argument := 238680386709389117458785239040, coefficient := (-238680386709389117458785239040) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
