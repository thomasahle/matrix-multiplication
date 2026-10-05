import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 11, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

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
def constantNumerator : ℤ := (-60608918032209588263920194289664)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    629061, 5397, 10785, 2691, 10785, 12268383,
    1915065, 1914795, 1914165, 1914795, 20303, 80975,
    40211, 80975, 61500781, 250007149, 2502703643, 105528983,
    10319869, 105528983, 210725067, 61773949, 250007149, 10319869,
    24536757, 69207027, 69206955, 69206787, 69206955, 6425,
    25625, 12725, 25625, 1848393751, 43848905107, 34957369217,
    18508792169, 1810008067, 18508792169, 36959196981, 1848598627, 43848905107,
    1810008067, 771, 3075, 1527, 3075, 20259111,
    915674961, 2545905, 61500781, 1848393751, 20259111, 52247181,
    43717029, 1223010543, 1847327699, 43717029, 39451953, 20259111,
    20259111, 39451953, 1223010543, 39451953
  ]
def negativeCoefficients : Array ℕ := #[
    2970656582080461887772819456, 101946447632189900873269248, 101861445035498247259422720, 101663105643217722160447488, 101861445035498247259422720, 115871601356415493111478747136,
    9043638768516757111166730240, 9042363729566382306959032320, 9039388638682174430474403840, 9042363729566382306959032320, 767025653613619254189359104, 764787251900739042358067200,
    759564314570685214751719424, 764787251900739042358067200, 70905572965016186971488256, 288238618387548178349031424, 2885420849672597209578733568, 243333267719980752427810816,
    11897998894825557295366144, 243333267719980752427810816, 242949461304018637676347392, 71220514226586630146228224, 288238618387548178349031424, 11897998894825557295366144,
    115871558855117147284671823872, 81705236170963643446169960448, 81705151168366951792556113920, 81704952828974671267457138688, 81705151168366951792556113920, 485459274438999527967948800,
    484042564494138634403840000, 480736907956129882754252800, 484042564494138634403840000, 2131052904508813662251646976, 50554345651325296393093906432, 40303102714760716166251937792,
    42678369031877813466340261888, 2086797223956170689994555392, 42678369031877813466340261888, 42611052992395356347308179456, 2131289110454991494632701952, 50554345651325296393093906432,
    2086797223956170689994555392, 29127556466339971678076928, 29042553869648318064230400, 28844214477367792965255168, 29042553869648318064230400, 46714329472234248493596672,
    2111402707533871850163535872, 46963657970977516006932480, 70905572965016186971488256, 2131052904508813662251646976, 46714329472234248493596672, 60236898529986267794374656,
    806436845625938605573668864, 1410035155385596921635667968, 2129823830232984523819188224, 806436845625938605573668864, 45485005012438610375344128, 46714329472234248493596672,
    46714329472234248493596672, 45485005012438610375344128, 1410035155385596921635667968, 45485005012438610375344128
  ]
def negativeScales : Array ℕ := #[
    19, 12, 13, 11, 13, 23,
    20, 20, 20, 20, 14, 16,
    15, 16, 25, 27, 31, 26,
    23, 26, 27, 25, 27, 23,
    24, 26, 26, 26, 26, 12,
    14, 13, 14, 30, 35, 35,
    34, 30, 34, 35, 30, 35,
    30, 9, 11, 10, 11, 24,
    29, 21, 25, 30, 24, 25,
    25, 30, 30, 25, 25, 24,
    24, 25, 30, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19262840396359288, 12397941971972645, 13396738556047823, 11393926675640423, 13396738556047823, 23548441775348019,
    20868961931881295, 20868758515735728, 20868283766495419, 20868758515735728, 14309405297370982, 16305188942569912,
    15295302594252799, 16305188942569912, 25874101398326001, 27897394112871740, 31220840318768995, 26653064041351958,
    23298921321576397, 26653064041351958, 27650786700639600, 25880495227539798, 27897394112871740, 23298921321576397,
    24548441246172424, 26044415194896637, 26044413693978284, 26044410191829388, 26044413693978284, 12649480738989629,
    14645264384186412, 13635378035865042, 14645264384186412, 30783624971647842, 35351821768364106, 35024877565050813,
    34107491700989241, 30753348981478623, 34107491700989241, 35105214360278175, 30783784871134843, 35351821768364106,
    30753348981478623, 9590587049919383, 11586370695117825, 10576484346799762, 11586370695117825, 24272067532129899,
    29770260332253290, 21279747155654583, 25874101398326001, 30783624971647842, 24272067532129899, 25638849862817523,
    25381692023304400, 30187789694702138, 30782792664336886, 25381692023304400, 25233593384315263, 24272067532129899,
    24272067532129899, 25233593384315263, 30187789694702138, 25233593384315263
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
noncomputable def negativeCeiling : ℝ := 151022897 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2970656582080461887772819456, coefficient := (-2970656582080461887772819456) }, { argument := 101946447632189900873269248, coefficient := (-101946447632189900873269248) }, { argument := 101861445035498247259422720, coefficient := (-101861445035498247259422720) }, { argument := 101663105643217722160447488, coefficient := (-101663105643217722160447488) }, { argument := 101861445035498247259422720, coefficient := (-101861445035498247259422720) }, { argument := 115871601356415493111478747136, coefficient := (-115871601356415493111478747136) }, { argument := 9043638768516757111166730240, coefficient := (-9043638768516757111166730240) }, { argument := 9042363729566382306959032320, coefficient := (-9042363729566382306959032320) }, { argument := 9039388638682174430474403840, coefficient := (-9039388638682174430474403840) }, { argument := 9042363729566382306959032320, coefficient := (-9042363729566382306959032320) }, { argument := 767025653613619254189359104, coefficient := (-767025653613619254189359104) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 759564314570685214751719424, coefficient := (-759564314570685214751719424) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 70905572965016186971488256, coefficient := (-70905572965016186971488256) }, { argument := 288238618387548178349031424, coefficient := (-288238618387548178349031424) }, { argument := 2885420849672597209578733568, coefficient := (-2885420849672597209578733568) }, { argument := 243333267719980752427810816, coefficient := (-243333267719980752427810816) }, { argument := 11897998894825557295366144, coefficient := (-11897998894825557295366144) }, { argument := 243333267719980752427810816, coefficient := (-243333267719980752427810816) }, { argument := 242949461304018637676347392, coefficient := (-242949461304018637676347392) }, { argument := 71220514226586630146228224, coefficient := (-71220514226586630146228224) }, { argument := 288238618387548178349031424, coefficient := (-288238618387548178349031424) }, { argument := 11897998894825557295366144, coefficient := (-11897998894825557295366144) }, { argument := 115871558855117147284671823872, coefficient := (-115871558855117147284671823872) }, { argument := 81705236170963643446169960448, coefficient := (-81705236170963643446169960448) }, { argument := 81705151168366951792556113920, coefficient := (-81705151168366951792556113920) }, { argument := 81704952828974671267457138688, coefficient := (-81704952828974671267457138688) }, { argument := 81705151168366951792556113920, coefficient := (-81705151168366951792556113920) }, { argument := 485459274438999527967948800, coefficient := (-485459274438999527967948800) }, { argument := 484042564494138634403840000, coefficient := (-484042564494138634403840000) }, { argument := 480736907956129882754252800, coefficient := (-480736907956129882754252800) }, { argument := 484042564494138634403840000, coefficient := (-484042564494138634403840000) }, { argument := 2131052904508813662251646976, coefficient := (-2131052904508813662251646976) }, { argument := 50554345651325296393093906432, coefficient := (-50554345651325296393093906432) }, { argument := 40303102714760716166251937792, coefficient := (-40303102714760716166251937792) }, { argument := 42678369031877813466340261888, coefficient := (-42678369031877813466340261888) }, { argument := 2086797223956170689994555392, coefficient := (-2086797223956170689994555392) }, { argument := 42678369031877813466340261888, coefficient := (-42678369031877813466340261888) }, { argument := 42611052992395356347308179456, coefficient := (-42611052992395356347308179456) }, { argument := 2131289110454991494632701952, coefficient := (-2131289110454991494632701952) }, { argument := 50554345651325296393093906432, coefficient := (-50554345651325296393093906432) }, { argument := 2086797223956170689994555392, coefficient := (-2086797223956170689994555392) }, { argument := 29127556466339971678076928, coefficient := (-29127556466339971678076928) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 28844214477367792965255168, coefficient := (-28844214477367792965255168) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 70905572965016186971488256, coefficient := (-70905572965016186971488256) }, { argument := 2131052904508813662251646976, coefficient := (-2131052904508813662251646976) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 60236898529986267794374656, coefficient := (-60236898529986267794374656) }, { argument := 806436845625938605573668864, coefficient := (-806436845625938605573668864) }, { argument := 1410035155385596921635667968, coefficient := (-1410035155385596921635667968) }, { argument := 2129823830232984523819188224, coefficient := (-2129823830232984523819188224) }, { argument := 806436845625938605573668864, coefficient := (-806436845625938605573668864) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 1410035155385596921635667968, coefficient := (-1410035155385596921635667968) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }] }

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
def constantNumerator : ℤ := (-51131879475950492557481579905024)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    15375141, 52247181, 20303, 80975, 40211, 80975,
    40349, 160925, 79913, 160925, 52247181, 2361477531,
    6565755, 6425, 25625, 12725, 25625, 622711,
    2483575, 1233307, 2483575, 43717029, 1975930179, 5493795,
    39835, 158875, 78895, 158875, 1223010543, 55277851593,
    153692265, 250007149, 43848905107, 10962227591, 62500473, 78633,
    7660265, 7659185, 7656665, 7659185, 1847327699, 10962227591,
    34909179781, 4627198597, 452502071, 4627198597, 9239800353, 461881721,
    10962227591, 452502071, 20303, 80975, 40211, 80975,
    43717029, 1975930179, 5493795, 2502703643, 34957369217, 915674961,
    2361477531, 1975930179, 55277851593, 34909179781
  ]
def negativeCoefficients : Array ℕ := #[
    70905322781049687285694464, 60236898529986267794374656, 767025653613619254189359104, 764787251900739042358067200, 759564314570685214751719424, 764787251900739042358067200,
    762171060869229258909679616, 759946826255797656014028800, 754756945491123915924176896, 759946826255797656014028800, 60236898529986267794374656, 2722598228135782122579296256,
    60558401067839428535255040, 485459274438999527967948800, 484042564494138634403840000, 480736907956129882754252800, 484042564494138634403840000, 11762678219656958562663399424,
    11728351337692979111605043200, 11648255279777027059135545344, 11728351337692979111605043200, 806436845625938605573668864, 36449478319532103518612619264, 810741042867401328961781760,
    752461875380449268350320640, 750265974965914883325952000, 745142207332001318269091840, 750265974965914883325952000, 1410035155385596921635667968, 63731023830035552950988832768,
    1417560939281873969998725120, 288238618387548178349031424, 50554345651325296393093906432, 50554351712233646111288459264, 288232557479198460154478592, 2970670749179910496708460544,
    9043644671474860698223247360, 9042369632524485894015549440, 9039394541640278017530920960, 9042369632524485894015549440, 2129823830232984523819188224, 50554351712233646111288459264,
    40247544077701440808740192256, 42678374148543450911527141376, 2086797474140137189680349184, 42678374148543450911527141376, 42611058100990543260247130112, 2130053474902879638634102784,
    50554351712233646111288459264, 2086797474140137189680349184, 767025653613619254189359104, 764787251900739042358067200, 759564314570685214751719424, 764787251900739042358067200,
    806436845625938605573668864, 36449478319532103518612619264, 810741042867401328961781760, 2885420849672597209578733568, 40303102714760716166251937792, 2111402707533871850163535872,
    2722598228135782122579296256, 36449478319532103518612619264, 63731023830035552950988832768, 40247544077701440808740192256
  ]
def negativeScales : Array ℕ := #[
    23, 25, 14, 16, 15, 16,
    15, 17, 16, 17, 25, 31,
    22, 12, 14, 13, 14, 19,
    21, 20, 21, 25, 30, 22,
    15, 17, 16, 17, 30, 35,
    27, 27, 35, 33, 25, 16,
    22, 22, 22, 22, 30, 33,
    35, 32, 28, 32, 33, 28,
    33, 28, 14, 16, 15, 16,
    25, 30, 22, 31, 35, 29,
    31, 30, 35, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23874096307896467, 25638849862817523, 14309405297370982, 16305188942569912, 15295302594252799, 16305188942569912,
    15300245298085506, 17296028943284436, 16286142594967323, 17296028943284436, 25638849862817523, 31137042662576968,
    22646529486345706, 12649480738989629, 14645264384186412, 13635378035865042, 14645264384186412, 19248203238645225,
    21243986883844155, 20234100535527042, 21243986883844155, 25381692023304400, 30879884826111423, 22389371646829086,
    15281748954468116, 17277532599667047, 16267646251349933, 17277532599667047, 30187789694702138, 35685982494529454,
    27195469318226823, 27897394112871740, 35351821768364106, 33351821941327316, 25897363776426689, 16262847276574088,
    22868962873556014, 22868759457543230, 22868284708612893, 22868759457543230, 30782792664336886, 33351821941327316,
    35022887408892757, 32107491873952451, 28753349154441834, 32107491873952451, 33105214533241385, 28782948212117327,
    33351821941327316, 28753349154441834, 14309405297370982, 16305188942569912, 15295302594252799, 16305188942569912,
    25381692023304400, 30879884826111423, 22389371646829086, 31220840318768995, 35024877565050813, 29770260332253290,
    31137042662576968, 30879884826111423, 35685982494529454, 35022887408892757
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
noncomputable def negativeCeiling : ℝ := 19529887 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 70905322781049687285694464, coefficient := (-70905322781049687285694464) }, { argument := 60236898529986267794374656, coefficient := (-60236898529986267794374656) }, { argument := 767025653613619254189359104, coefficient := (-767025653613619254189359104) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 759564314570685214751719424, coefficient := (-759564314570685214751719424) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 762171060869229258909679616, coefficient := (-762171060869229258909679616) }, { argument := 759946826255797656014028800, coefficient := (-759946826255797656014028800) }, { argument := 754756945491123915924176896, coefficient := (-754756945491123915924176896) }, { argument := 759946826255797656014028800, coefficient := (-759946826255797656014028800) }, { argument := 60236898529986267794374656, coefficient := (-60236898529986267794374656) }, { argument := 2722598228135782122579296256, coefficient := (-2722598228135782122579296256) }, { argument := 60558401067839428535255040, coefficient := (-60558401067839428535255040) }, { argument := 485459274438999527967948800, coefficient := (-485459274438999527967948800) }, { argument := 484042564494138634403840000, coefficient := (-484042564494138634403840000) }, { argument := 480736907956129882754252800, coefficient := (-480736907956129882754252800) }, { argument := 484042564494138634403840000, coefficient := (-484042564494138634403840000) }, { argument := 11762678219656958562663399424, coefficient := (-11762678219656958562663399424) }, { argument := 11728351337692979111605043200, coefficient := (-11728351337692979111605043200) }, { argument := 11648255279777027059135545344, coefficient := (-11648255279777027059135545344) }, { argument := 11728351337692979111605043200, coefficient := (-11728351337692979111605043200) }, { argument := 806436845625938605573668864, coefficient := (-806436845625938605573668864) }, { argument := 36449478319532103518612619264, coefficient := (-36449478319532103518612619264) }, { argument := 810741042867401328961781760, coefficient := (-810741042867401328961781760) }, { argument := 752461875380449268350320640, coefficient := (-752461875380449268350320640) }, { argument := 750265974965914883325952000, coefficient := (-750265974965914883325952000) }, { argument := 745142207332001318269091840, coefficient := (-745142207332001318269091840) }, { argument := 750265974965914883325952000, coefficient := (-750265974965914883325952000) }, { argument := 1410035155385596921635667968, coefficient := (-1410035155385596921635667968) }, { argument := 63731023830035552950988832768, coefficient := (-63731023830035552950988832768) }, { argument := 1417560939281873969998725120, coefficient := (-1417560939281873969998725120) }, { argument := 288238618387548178349031424, coefficient := (-288238618387548178349031424) }, { argument := 50554345651325296393093906432, coefficient := (-50554345651325296393093906432) }, { argument := 50554351712233646111288459264, coefficient := (-50554351712233646111288459264) }, { argument := 288232557479198460154478592, coefficient := (-288232557479198460154478592) }, { argument := 2970670749179910496708460544, coefficient := (-2970670749179910496708460544) }, { argument := 9043644671474860698223247360, coefficient := (-9043644671474860698223247360) }, { argument := 9042369632524485894015549440, coefficient := (-9042369632524485894015549440) }, { argument := 9039394541640278017530920960, coefficient := (-9039394541640278017530920960) }, { argument := 9042369632524485894015549440, coefficient := (-9042369632524485894015549440) }, { argument := 2129823830232984523819188224, coefficient := (-2129823830232984523819188224) }, { argument := 50554351712233646111288459264, coefficient := (-50554351712233646111288459264) }, { argument := 40247544077701440808740192256, coefficient := (-40247544077701440808740192256) }, { argument := 42678374148543450911527141376, coefficient := (-42678374148543450911527141376) }, { argument := 2086797474140137189680349184, coefficient := (-2086797474140137189680349184) }, { argument := 42678374148543450911527141376, coefficient := (-42678374148543450911527141376) }, { argument := 42611058100990543260247130112, coefficient := (-42611058100990543260247130112) }, { argument := 2130053474902879638634102784, coefficient := (-2130053474902879638634102784) }, { argument := 50554351712233646111288459264, coefficient := (-50554351712233646111288459264) }, { argument := 2086797474140137189680349184, coefficient := (-2086797474140137189680349184) }, { argument := 767025653613619254189359104, coefficient := (-767025653613619254189359104) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 759564314570685214751719424, coefficient := (-759564314570685214751719424) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 806436845625938605573668864, coefficient := (-806436845625938605573668864) }, { argument := 36449478319532103518612619264, coefficient := (-36449478319532103518612619264) }, { argument := 810741042867401328961781760, coefficient := (-810741042867401328961781760) }, { argument := 2885420849672597209578733568, coefficient := (-2885420849672597209578733568) }, { argument := 40303102714760716166251937792, coefficient := (-40303102714760716166251937792) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 2722598228135782122579296256, coefficient := (-2722598228135782122579296256) }, { argument := 36449478319532103518612619264, coefficient := (-36449478319532103518612619264) }, { argument := 63731023830035552950988832768, coefficient := (-63731023830035552950988832768) }, { argument := 40247544077701440808740192256, coefficient := (-40247544077701440808740192256) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
