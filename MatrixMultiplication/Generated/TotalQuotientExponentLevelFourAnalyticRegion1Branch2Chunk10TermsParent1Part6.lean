import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 2,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 103805786763827208280606299792605184
def positiveArguments : Array ℕ := #[
    27195, 1911, 1715, 27195, 245, 1911,
    1911, 1911, 1911, 1911, 2205, 2303,
    575, 2415, 10465, 345, 345, 805,
    10465, 10465, 345, 129145, 5175, 2415,
    10465, 805, 5175, 805, 10465, 10465,
    345, 1, 616562751, 616562625, 8075415191, 28040356611,
    4037707571, 8153085977, 5405, 148930712831, 133745, 4255,
    297852929631, 2185, 2185, 73945, 4025, 133745,
    73945, 4080794565, 4255, 4025, 5405, 199949819,
    11973978175, 211905, 494032661993, 217445
  ]
def positiveCoefficients : Array ℕ := #[
    1052055605261434892996302602240, 2365703415074361705332226392064, 66345848980450849107874938880, 1052055605261434892996302602240, 75823827406229541837571358720, 73928231721073803291632074752,
    73928231721073803291632074752, 73928231721073803291632074752, 2365703415074361705332226392064, 73928231721073803291632074752, 85301805832008234567267778560, 89092997202319711659146346496,
    11122117540454588407296819200, 186851574679637085242586562560, 404845078472547018025604218880, 13346541048545506088756183040, 213544656776728097420098928640, 15570964556636423770215546880,
    404845078472547018025604218880, 404845078472547018025604218880, 213544656776728097420098928640, 4996055199172201112557731184640, 400396231456365182662685491200, 186851574679637085242586562560,
    404845078472547018025604218880, 15570964556636423770215546880, 400396231456365182662685491200, 15570964556636423770215546880, 404845078472547018025604218880, 404845078472547018025604218880,
    13346541048545506088756183040, 158456325028528675187087900672, 5823270539816605654700777275392, 5823269349780251971550183424000, 76270140066469548462922239311872, 264833680454997348838170282688512,
    76270139603677633141697008369664, 38501859949739315110750025940992, 104547904880273131028590100480, 1406610813085997224255625208266752, 2587004539909737263537240145920, 82303669799363954213996462080,
    1406570691713965402780930645426176, 84528093307454871895455825920, 84528093307454871895455825920, 1430304315702460069178370949120, 77854822783182118851077734400, 2587004539909737263537240145920,
    1430304315702460069178370949120, 38542014954465227583057800724480, 82303669799363954213996462080, 77854822783182118851077734400, 104547904880273131028590100480, 1888472647002904322145463042048,
    226182052800930572635156460339200, 4098838812887007924257795604480, 2333003284438611658537706222256128, 4205997997537648654303751045120
  ]
def positiveScales : Array ℕ := #[
    14, 10, 10, 14, 7, 10,
    10, 10, 10, 10, 11, 11,
    9, 11, 13, 8, 8, 9,
    13, 13, 8, 16, 12, 11,
    13, 9, 12, 9, 13, 13,
    8, 0, 29, 29, 32, 34,
    31, 32, 12, 37, 17, 12,
    38, 11, 11, 16, 11, 17,
    16, 31, 12, 11, 12, 27,
    33, 17, 38, 17
  ]
def negativeArguments : Array ℕ := #[
    49, 115, 1, 147, 1317, 18295
  ]
def negativeCoefficients : Array ℕ := #[
    7764359926397905084167307132928, 9111238689140398823257554288640, 158456325028528675187087900672, 11646539889596857626250960699392, 417373960125144530442789530370048, 2898958466396932112547773142794240
  ]
def negativeScales : Array ℕ := #[
    5, 6, 0, 7, 10, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14731053805343505, 10900112062706946, 10743992861047947, 14731053805343505, 7936637938489789, 10900112062706946,
    10900112062706946, 10900112062706946, 10900112062706946, 10900112062706946, 11106562940444882, 11169298695792845,
    9167418145831737, 11237807473723135, 13353284691143071, 8430452551665529, 8430452551665529, 9652844973000555,
    13353284691143071, 13353284691143071, 8430452551665529, 16978632262310490, 12337343147274049, 11237807473723135,
    13353284691143071, 9652844973000555, 12337343147274049, 9652844973000555, 13353284691143071, 13353284691143071,
    8430452551665529, 0, 29199672492250057, 29199672197422655, 32910889290381337, 34706785646207251,
    31910889281627353, 32924699082364684, 12400078902622011, 37115850344221523, 17029125432417593, 12054943416573324,
    38115809193016477, 11093417564387960, 11093417564387960, 16174164978272322, 11974773066918090, 17029125432417593,
    16174164978272322, 31926202937955473, 12054943416573324, 11974773066918090, 12400078902622011, 27575062734280672,
    33479183494625500, 17693058103625387, 38845815469556248, 17730291009819162
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5614709844123661, 6845490052533228, 0, 7199672344836365, 10363039630256516, 14159161795226450
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 2666935146639 / 1000000000000
noncomputable def negativeCeiling : ℝ := 274215720947 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1052055605261434892996302602240, coefficient := 1052055605261434892996302602240 }, { argument := 2365703415074361705332226392064, coefficient := 2365703415074361705332226392064 }, { argument := 66345848980450849107874938880, coefficient := 66345848980450849107874938880 }, { argument := 1052055605261434892996302602240, coefficient := 1052055605261434892996302602240 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 2365703415074361705332226392064, coefficient := 2365703415074361705332226392064 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 85301805832008234567267778560, coefficient := 85301805832008234567267778560 }, { argument := 89092997202319711659146346496, coefficient := 89092997202319711659146346496 }, { argument := 7764359926397905084167307132928, coefficient := (-7764359926397905084167307132928) }, { argument := 11122117540454588407296819200, coefficient := 11122117540454588407296819200 }, { argument := 186851574679637085242586562560, coefficient := 186851574679637085242586562560 }, { argument := 404845078472547018025604218880, coefficient := 404845078472547018025604218880 }, { argument := 13346541048545506088756183040, coefficient := 13346541048545506088756183040 }, { argument := 213544656776728097420098928640, coefficient := 213544656776728097420098928640 }, { argument := 15570964556636423770215546880, coefficient := 15570964556636423770215546880 }, { argument := 404845078472547018025604218880, coefficient := 404845078472547018025604218880 }, { argument := 404845078472547018025604218880, coefficient := 404845078472547018025604218880 }, { argument := 213544656776728097420098928640, coefficient := 213544656776728097420098928640 }, { argument := 4996055199172201112557731184640, coefficient := 4996055199172201112557731184640 }, { argument := 400396231456365182662685491200, coefficient := 400396231456365182662685491200 }, { argument := 186851574679637085242586562560, coefficient := 186851574679637085242586562560 }, { argument := 404845078472547018025604218880, coefficient := 404845078472547018025604218880 }, { argument := 15570964556636423770215546880, coefficient := 15570964556636423770215546880 }, { argument := 400396231456365182662685491200, coefficient := 400396231456365182662685491200 }, { argument := 15570964556636423770215546880, coefficient := 15570964556636423770215546880 }, { argument := 404845078472547018025604218880, coefficient := 404845078472547018025604218880 }, { argument := 404845078472547018025604218880, coefficient := 404845078472547018025604218880 }, { argument := 13346541048545506088756183040, coefficient := 13346541048545506088756183040 }, { argument := 9111238689140398823257554288640, coefficient := (-9111238689140398823257554288640) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 5823270539816605654700777275392, coefficient := 5823270539816605654700777275392 }, { argument := 5823269349780251971550183424000, coefficient := 5823269349780251971550183424000 }, { argument := 11646539889596857626250960699392, coefficient := (-11646539889596857626250960699392) }, { argument := 76270140066469548462922239311872, coefficient := 76270140066469548462922239311872 }, { argument := 264833680454997348838170282688512, coefficient := 264833680454997348838170282688512 }, { argument := 76270139603677633141697008369664, coefficient := 76270139603677633141697008369664 }, { argument := 417373960125144530442789530370048, coefficient := (-417373960125144530442789530370048) }, { argument := 38501859949739315110750025940992, coefficient := 38501859949739315110750025940992 }, { argument := 104547904880273131028590100480, coefficient := 104547904880273131028590100480 }, { argument := 1406610813085997224255625208266752, coefficient := 1406610813085997224255625208266752 }, { argument := 2587004539909737263537240145920, coefficient := 2587004539909737263537240145920 }, { argument := 82303669799363954213996462080, coefficient := 82303669799363954213996462080 }, { argument := 1406570691713965402780930645426176, coefficient := 1406570691713965402780930645426176 }, { argument := 84528093307454871895455825920, coefficient := 84528093307454871895455825920 }, { argument := 84528093307454871895455825920, coefficient := 84528093307454871895455825920 }, { argument := 1430304315702460069178370949120, coefficient := 1430304315702460069178370949120 }, { argument := 77854822783182118851077734400, coefficient := 77854822783182118851077734400 }, { argument := 2587004539909737263537240145920, coefficient := 2587004539909737263537240145920 }, { argument := 1430304315702460069178370949120, coefficient := 1430304315702460069178370949120 }, { argument := 38542014954465227583057800724480, coefficient := 38542014954465227583057800724480 }, { argument := 82303669799363954213996462080, coefficient := 82303669799363954213996462080 }, { argument := 77854822783182118851077734400, coefficient := 77854822783182118851077734400 }, { argument := 104547904880273131028590100480, coefficient := 104547904880273131028590100480 }, { argument := 2898958466396932112547773142794240, coefficient := (-2898958466396932112547773142794240) }, { argument := 1888472647002904322145463042048, coefficient := 1888472647002904322145463042048 }, { argument := 226182052800930572635156460339200, coefficient := 226182052800930572635156460339200 }, { argument := 4098838812887007924257795604480, coefficient := 4098838812887007924257795604480 }, { argument := 2333003284438611658537706222256128, coefficient := 2333003284438611658537706222256128 }, { argument := 4205997997537648654303751045120, coefficient := 4205997997537648654303751045120 }] }

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

end TermShard12


end Parent1

namespace Parent1

namespace TermShard13

/-! Directed signed-log shard 13.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-261559698855630558954402542379859968)
def positiveArguments : Array ℕ := #[
    6925, 211905, 120495, 217445, 3394635, 4155,
    5986990819, 211905, 6925, 4155, 6925, 106645,
    120495, 399896077, 569307077, 32224079931, 22855, 20243,
    947503, 257935, 16112042919, 947503, 22855, 22855,
    9795, 22855, 257935, 9795, 284650585, 20243,
    111254307, 31563, 616074461, 50841, 1575, 50841,
    33957, 111512355, 31563, 189, 535, 489,
    535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    133948980813300912557444300800, 4098838812887007924257795604480, 2330712266151435878499530833920, 4205997997537648654303751045120, 65661790394680107335659196252160, 2571820431615377521102930575360,
    226182118215151093345481960456192, 4098838812887007924257795604480, 133948980813300912557444300800, 2571820431615377521102930575360, 133948980813300912557444300800, 4125628609049668106769284464640,
    2330712266151435878499530833920, 1888455830655858823338857070592, 2688476658885288288636310126592, 152173915007466789619751479934976, 884159987433355193213108879360, 783113131726686028274467864576,
    36654746907594239581492028112896, 9978377001033580037690800209920, 152173942902485603930745757237248, 36654746907594239581492028112896, 884159987433355193213108879360, 884159987433355193213108879360,
    757851417800018737039807610880, 884159987433355193213108879360, 9978377001033580037690800209920, 757851417800018737039807610880, 2688448763866473977642032824320, 783113131726686028274467864576,
    525383610451689749585615388672, 610517210311944650260016529408, 5818658771156764816577986035712, 983407961520437789939787104256, 30464930654288655202595635200, 983407961520437789939787104256,
    656823904906463406167961894912, 526602207677861295793719214080, 610517210311944650260016529408, 29246333428117108994491809792, 41393620063604902941939466240, 37834542450659434651604484096,
    41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    12, 17, 16, 17, 21, 12,
    32, 17, 12, 12, 12, 16,
    16, 28, 29, 34, 14, 14,
    19, 17, 33, 19, 14, 14,
    13, 14, 17, 13, 28, 14,
    26, 14, 29, 15, 10, 15,
    15, 26, 14, 7, 9, 8,
    9, 8
  ]
def negativeArguments : Array ℕ := #[
    36475, 2585, 17, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2889847227707791713724515588505600, 409609600198746625358622223237120, 10775030101939949912721977245696, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    15, 11, 4, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12757598355807462, 17693058103625387, 16878613756602126, 17730291009819162, 21694825029799412, 12020632761657706,
    32479183911867968, 17693058103625387, 12757598355807462, 12020632761657706, 12757598355807462, 16702456801626690,
    16878613756602126, 28575049887407541, 29084631792938874, 34907420115595137, 14480222198491388, 14305135491933305,
    19853770985498009, 17976648023609385, 33907420380055714, 19853770985498009, 14480222198491388, 14480222198491388,
    13257829777154949, 14480222198491388, 17976648023609385, 13257829777154949, 28084616823787493, 14305135491933305,
    26729285947459133, 14945946716094235, 29198529489927061, 15633704786776826, 10621136113274016, 15633704786776826,
    15051421386252421, 26732628321340467, 14945946716094235, 7562242424220952, 9063395081288509, 8933690654464738,
    9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    15154620357692616, 11335948565202298, 4087462841250340, 0
  ]

abbrev PositiveTerm := Fin 44
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
noncomputable def positiveFloor : ℝ := 13271573571 / 50000000000
noncomputable def negativeCeiling : ℝ := 583579565597 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 133948980813300912557444300800, coefficient := 133948980813300912557444300800 }, { argument := 4098838812887007924257795604480, coefficient := 4098838812887007924257795604480 }, { argument := 2330712266151435878499530833920, coefficient := 2330712266151435878499530833920 }, { argument := 4205997997537648654303751045120, coefficient := 4205997997537648654303751045120 }, { argument := 65661790394680107335659196252160, coefficient := 65661790394680107335659196252160 }, { argument := 2571820431615377521102930575360, coefficient := 2571820431615377521102930575360 }, { argument := 226182118215151093345481960456192, coefficient := 226182118215151093345481960456192 }, { argument := 4098838812887007924257795604480, coefficient := 4098838812887007924257795604480 }, { argument := 133948980813300912557444300800, coefficient := 133948980813300912557444300800 }, { argument := 2571820431615377521102930575360, coefficient := 2571820431615377521102930575360 }, { argument := 133948980813300912557444300800, coefficient := 133948980813300912557444300800 }, { argument := 4125628609049668106769284464640, coefficient := 4125628609049668106769284464640 }, { argument := 2330712266151435878499530833920, coefficient := 2330712266151435878499530833920 }, { argument := 1888455830655858823338857070592, coefficient := 1888455830655858823338857070592 }, { argument := 2889847227707791713724515588505600, coefficient := (-2889847227707791713724515588505600) }, { argument := 2688476658885288288636310126592, coefficient := 2688476658885288288636310126592 }, { argument := 152173915007466789619751479934976, coefficient := 152173915007466789619751479934976 }, { argument := 884159987433355193213108879360, coefficient := 884159987433355193213108879360 }, { argument := 783113131726686028274467864576, coefficient := 783113131726686028274467864576 }, { argument := 36654746907594239581492028112896, coefficient := 36654746907594239581492028112896 }, { argument := 9978377001033580037690800209920, coefficient := 9978377001033580037690800209920 }, { argument := 152173942902485603930745757237248, coefficient := 152173942902485603930745757237248 }, { argument := 36654746907594239581492028112896, coefficient := 36654746907594239581492028112896 }, { argument := 884159987433355193213108879360, coefficient := 884159987433355193213108879360 }, { argument := 884159987433355193213108879360, coefficient := 884159987433355193213108879360 }, { argument := 757851417800018737039807610880, coefficient := 757851417800018737039807610880 }, { argument := 884159987433355193213108879360, coefficient := 884159987433355193213108879360 }, { argument := 9978377001033580037690800209920, coefficient := 9978377001033580037690800209920 }, { argument := 757851417800018737039807610880, coefficient := 757851417800018737039807610880 }, { argument := 2688448763866473977642032824320, coefficient := 2688448763866473977642032824320 }, { argument := 783113131726686028274467864576, coefficient := 783113131726686028274467864576 }, { argument := 409609600198746625358622223237120, coefficient := (-409609600198746625358622223237120) }, { argument := 525383610451689749585615388672, coefficient := 525383610451689749585615388672 }, { argument := 610517210311944650260016529408, coefficient := 610517210311944650260016529408 }, { argument := 5818658771156764816577986035712, coefficient := 5818658771156764816577986035712 }, { argument := 983407961520437789939787104256, coefficient := 983407961520437789939787104256 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 983407961520437789939787104256, coefficient := 983407961520437789939787104256 }, { argument := 656823904906463406167961894912, coefficient := 656823904906463406167961894912 }, { argument := 526602207677861295793719214080, coefficient := 526602207677861295793719214080 }, { argument := 610517210311944650260016529408, coefficient := 610517210311944650260016529408 }, { argument := 29246333428117108994491809792, coefficient := 29246333428117108994491809792 }, { argument := 10775030101939949912721977245696, coefficient := (-10775030101939949912721977245696) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard13


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
