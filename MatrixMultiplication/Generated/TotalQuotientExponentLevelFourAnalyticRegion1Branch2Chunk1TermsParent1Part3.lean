import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

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
def constantNumerator : ℤ := (-213463717736118793294023193788416)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    682285156875, 31648837815, 603707355, 22735864645, 397849288655, 397849483785,
    22735669515, 1561524825, 42711673395, 12492194565, 863387265, 15108200835,
    15108208245, 863379855, 1042951525, 28527375415, 8343609505, 42122607,
    2750813125, 135820089, 23544828635, 139370941, 4438565, 135820089,
    77231031, 139370941, 2175784563, 2663139, 1375407395, 135820089,
    4438565, 2663139, 4438565, 68353901, 77231031, 42122607,
    2242670893, 6979641, 35340382391, 172708989, 5494611, 35340399681,
    2821557, 2821557, 95487429, 5197605, 172708989, 95487429,
    2242653603, 5494611, 5197605, 6979641, 25154675, 688044305,
    201237335, 1784333681, 31223615059, 31223630373, 1784318367, 969422475,
    26516168985, 7755377295, 5804925, 158779455
  ]
def negativeCoefficients : Array ℕ := #[
    786621229635243624219279360000, 72977251425455750563894394880, 696027192068819902770708480, 26212667275051016786563563520, 917378000965772749688075714560, 917378450904919137556176568320,
    26212442305477822852513136640, 14402524405759547344001433600, 49243206754839635919655403520, 14402519753721276255373885440, 1990835489244381021764321280, 69674278554362487318081699840,
    69674312726955883865026068480, 1990818402947682748292136960, 9619529931480044632486707200, 32889824585946175663809495040, 9619526824356589717034106880, 97128118880805809358372864,
    6342943213934525252894720000, 1252719210925726930317606912, 54290678511149150195175915520, 1285470039969536784704995328, 40938536304762317984235520, 1252719210925726930317606912,
    712330531702864332925698048, 1285470039969536784704995328, 20068070496594488275872251904, 786019897051436505297321984, 6342947053163135593695150080, 1252719210925726930317606912,
    40938536304762317984235520, 786019897051436505297321984, 40938536304762317984235520, 1260906918186679393914454016, 712330531702864332925698048, 97128118880805809358372864,
    2585623500295541121580269568, 257503302506740417101299712, 81489373679226080497323999232, 6371837038624236278485352448, 202715365803178626228682752, 81489413547251709802092429312,
    208194159473534805315944448, 208194159473534805315944448, 3522864330039023153109270528, 191757778462466268054159360, 6371837038624236278485352448, 3522864330039023153109270528,
    2585603566282726469196054528, 202715365803178626228682752, 191757778462466268054159360, 257503302506740417101299712, 464021851982339815296204800, 1586522150713544651686543360,
    464021702102544216406097920, 2057196672219193722489798656, 71996754506174570228684423168, 71996789817854413327193604096, 2057179016379272173235208192, 8941344147813547979361484800,
    30571061442595610403652239360, 8941341259745178939209809920, 428327863368313675658035200, 1464481985274041216941424640
  ]
def negativeScales : Array ℕ := #[
    39, 34, 29, 34, 38, 38,
    34, 30, 35, 33, 29, 33,
    33, 29, 29, 34, 32, 25,
    31, 27, 34, 27, 22, 27,
    26, 27, 31, 21, 30, 27,
    22, 21, 22, 26, 26, 25,
    31, 22, 35, 27, 22, 35,
    21, 21, 26, 22, 27, 26,
    31, 22, 22, 22, 24, 29,
    27, 30, 34, 34, 30, 29,
    34, 32, 22, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39311583874546475, 34881433475048456, 29169274136789852, 34404250819696074, 38533431063254765, 38533431770841840,
    34404238437748179, 30540308359381406, 35313911371119063, 33540307893388539, 29685432572291307, 33814612816665734,
    33814613524252821, 29685420190343397, 29958024970784363, 34731627970743498, 32958024504791404, 25328091392825413,
    31357210988262979, 27017121641900989, 34454691171263281, 27054354548099964, 22081661894095700, 27017121641900989,
    26202677295057066, 27054354548099964, 31018888568075177, 21344696299929494, 30357211861490787, 27017121641900989,
    22081661894095700, 21344696299929494, 22081661894095700, 26026520339903239, 26202677295057066, 25328091392825413,
    31062570777632418, 22734721402360907, 35040598599137086, 27363767931996041, 22389585916151775, 35040599304963946,
    21428060063966427, 21428060063966427, 26508807477851131, 22309415567467788, 27363767931996041, 26508807477851131,
    31062559655049301, 22389585916151775, 22309415567467788, 22734721402360907, 24584323214247371, 29357926225982376,
    27584322748254505, 30732738287171960, 34861918532747236, 34861919240334340, 30732725905224023, 29852550291116229,
    34626153301047966, 32852549825123347, 22468845996823885, 27242449008562439
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
noncomputable def negativeCeiling : ℝ := 198205269 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 786621229635243624219279360000, coefficient := (-786621229635243624219279360000) }, { argument := 72977251425455750563894394880, coefficient := (-72977251425455750563894394880) }, { argument := 696027192068819902770708480, coefficient := (-696027192068819902770708480) }, { argument := 26212667275051016786563563520, coefficient := (-26212667275051016786563563520) }, { argument := 917378000965772749688075714560, coefficient := (-917378000965772749688075714560) }, { argument := 917378450904919137556176568320, coefficient := (-917378450904919137556176568320) }, { argument := 26212442305477822852513136640, coefficient := (-26212442305477822852513136640) }, { argument := 14402524405759547344001433600, coefficient := (-14402524405759547344001433600) }, { argument := 49243206754839635919655403520, coefficient := (-49243206754839635919655403520) }, { argument := 14402519753721276255373885440, coefficient := (-14402519753721276255373885440) }, { argument := 1990835489244381021764321280, coefficient := (-1990835489244381021764321280) }, { argument := 69674278554362487318081699840, coefficient := (-69674278554362487318081699840) }, { argument := 69674312726955883865026068480, coefficient := (-69674312726955883865026068480) }, { argument := 1990818402947682748292136960, coefficient := (-1990818402947682748292136960) }, { argument := 9619529931480044632486707200, coefficient := (-9619529931480044632486707200) }, { argument := 32889824585946175663809495040, coefficient := (-32889824585946175663809495040) }, { argument := 9619526824356589717034106880, coefficient := (-9619526824356589717034106880) }, { argument := 97128118880805809358372864, coefficient := (-97128118880805809358372864) }, { argument := 6342943213934525252894720000, coefficient := (-6342943213934525252894720000) }, { argument := 1252719210925726930317606912, coefficient := (-1252719210925726930317606912) }, { argument := 54290678511149150195175915520, coefficient := (-54290678511149150195175915520) }, { argument := 1285470039969536784704995328, coefficient := (-1285470039969536784704995328) }, { argument := 40938536304762317984235520, coefficient := (-40938536304762317984235520) }, { argument := 1252719210925726930317606912, coefficient := (-1252719210925726930317606912) }, { argument := 712330531702864332925698048, coefficient := (-712330531702864332925698048) }, { argument := 1285470039969536784704995328, coefficient := (-1285470039969536784704995328) }, { argument := 20068070496594488275872251904, coefficient := (-20068070496594488275872251904) }, { argument := 786019897051436505297321984, coefficient := (-786019897051436505297321984) }, { argument := 6342947053163135593695150080, coefficient := (-6342947053163135593695150080) }, { argument := 1252719210925726930317606912, coefficient := (-1252719210925726930317606912) }, { argument := 40938536304762317984235520, coefficient := (-40938536304762317984235520) }, { argument := 786019897051436505297321984, coefficient := (-786019897051436505297321984) }, { argument := 40938536304762317984235520, coefficient := (-40938536304762317984235520) }, { argument := 1260906918186679393914454016, coefficient := (-1260906918186679393914454016) }, { argument := 712330531702864332925698048, coefficient := (-712330531702864332925698048) }, { argument := 97128118880805809358372864, coefficient := (-97128118880805809358372864) }, { argument := 2585623500295541121580269568, coefficient := (-2585623500295541121580269568) }, { argument := 257503302506740417101299712, coefficient := (-257503302506740417101299712) }, { argument := 81489373679226080497323999232, coefficient := (-81489373679226080497323999232) }, { argument := 6371837038624236278485352448, coefficient := (-6371837038624236278485352448) }, { argument := 202715365803178626228682752, coefficient := (-202715365803178626228682752) }, { argument := 81489413547251709802092429312, coefficient := (-81489413547251709802092429312) }, { argument := 208194159473534805315944448, coefficient := (-208194159473534805315944448) }, { argument := 208194159473534805315944448, coefficient := (-208194159473534805315944448) }, { argument := 3522864330039023153109270528, coefficient := (-3522864330039023153109270528) }, { argument := 191757778462466268054159360, coefficient := (-191757778462466268054159360) }, { argument := 6371837038624236278485352448, coefficient := (-6371837038624236278485352448) }, { argument := 3522864330039023153109270528, coefficient := (-3522864330039023153109270528) }, { argument := 2585603566282726469196054528, coefficient := (-2585603566282726469196054528) }, { argument := 202715365803178626228682752, coefficient := (-202715365803178626228682752) }, { argument := 191757778462466268054159360, coefficient := (-191757778462466268054159360) }, { argument := 257503302506740417101299712, coefficient := (-257503302506740417101299712) }, { argument := 464021851982339815296204800, coefficient := (-464021851982339815296204800) }, { argument := 1586522150713544651686543360, coefficient := (-1586522150713544651686543360) }, { argument := 464021702102544216406097920, coefficient := (-464021702102544216406097920) }, { argument := 2057196672219193722489798656, coefficient := (-2057196672219193722489798656) }, { argument := 71996754506174570228684423168, coefficient := (-71996754506174570228684423168) }, { argument := 71996789817854413327193604096, coefficient := (-71996789817854413327193604096) }, { argument := 2057179016379272173235208192, coefficient := (-2057179016379272173235208192) }, { argument := 8941344147813547979361484800, coefficient := (-8941344147813547979361484800) }, { argument := 30571061442595610403652239360, coefficient := (-30571061442595610403652239360) }, { argument := 8941341259745178939209809920, coefficient := (-8941341259745178939209809920) }, { argument := 428327863368313675658035200, coefficient := (-428327863368313675658035200) }, { argument := 1464481985274041216941424640, coefficient := (-1464481985274041216941424640) }] }

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
def constantNumerator : ℤ := 8332416379185140483106585354174464
def positiveArguments : Array ℕ := #[
    431, 1160985, 31755891, 9287877, 133686787, 2303,
    2009619465, 56987, 1813, 2009620447, 931, 931,
    31507, 1715, 56987, 31507, 133685805, 1813,
    1715, 2303, 41639717, 2208129071, 171819, 15891410165,
    176311, 5615, 171819, 97701, 176311, 2752473,
    3369, 1104065097, 171819, 5615, 3369, 5615,
    86471, 97701, 41639717, 40046125, 442390995, 17185,
    15221, 712441, 193945, 221195571, 712441, 17185,
    17185, 7365, 17185, 193945, 7365, 20022989,
    15221, 75, 1503, 2523, 2421
  ]
def positiveCoefficients : Array ℕ := #[
    136589352174591718011269770379264, 175443092835661281549531217920, 599851821168247282459207532544, 175443036167263487113788653568, 631318002131333408448946634752, 89092997202319711659146346496,
    18980319209676856158175132385280, 2204577781836123928927387254784, 70137040350762326199753506816, 18980328484404628514158332084224, 72032636035918064745692790784, 72032636035918064745692790784,
    1218868025555139885038959591424, 66345848980450849107874938880, 2204577781836123928927387254784, 1218868025555139885038959591424, 631313364767447230457346785280, 70137040350762326199753506816,
    66345848980450849107874938880, 89092997202319711659146346496, 196638003916977374588705964032, 10427594714740487099818144956416, 3323462806405855522701447266304, 75045062728729978318872211619840,
    3410350722913198150745929547776, 108609895634178285055602851840, 3323462806405855522701447266304, 1889812184034702159967489622016, 3410350722913198150745929547776, 53240570839874195334256517971968,
    2085309996176223073067574755328, 10427600017958047362429719937024, 3323462806405855522701447266304, 108609895634178285055602851840, 2085309996176223073067574755328, 108609895634178285055602851840,
    3345184785532691179712567836672, 1889812184034702159967489622016, 196638003916977374588705964032, 378224956937616341866643456000, 4178264814222705602767922135040, 332406243361238437877210152960,
    294416958405668330691243278336, 13780613117633056381709483769856, 3751441889362548084614228869120, 4178266202598451566443614961664, 13780613117633056381709483769856, 332406243361238437877210152960,
    332406243361238437877210152960, 284919637166775803894751559680, 332406243361238437877210152960, 3751441889362548084614228869120, 284919637166775803894751559680, 378223568561870378190950629376,
    294416958405668330691243278336, 5802843934150220038589644800, 116288992440370409573336481792, 195207669944813402098155651072, 187315802194369102845673734144
  ]
def positiveScales : Array ℕ := #[
    8, 20, 24, 23, 26, 11,
    30, 15, 10, 30, 9, 9,
    14, 10, 15, 14, 26, 10,
    10, 11, 25, 31, 17, 33,
    17, 12, 17, 16, 17, 21,
    11, 30, 17, 12, 11, 12,
    16, 16, 25, 25, 28, 14,
    13, 19, 17, 27, 19, 14,
    14, 12, 14, 17, 12, 24,
    13, 6, 10, 11, 11
  ]
def negativeArguments : Array ℕ := #[
    46439385, 3, 589, 1123, 589
  ]
def negativeCoefficients : Array ℕ := #[
    428327725017733122836398080, 950737950171172051122527404032, 46665387720901694842597386747904, 177946453007037702235099712454656, 46665387720901694842597386747904
  ]
def negativeScales : Array ℕ := #[
    25, 1, 9, 10, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8751544059074671, 20146917901936429, 24920520913287028, 23146917435943563, 26994281640762934, 11169298695792845,
    30904275196923883, 15798345225549727, 10824163209679199, 30904275901896243, 9862637357422660, 9862637357422660,
    14943384770867824, 10743992861047947, 15798345225549727, 14943384770867824, 26994271043367821, 10824163209679199,
    10743992861047947, 11169298695792845, 25311456927755590, 31040177357918140, 17390530055093252, 33887528100266077,
    17427762961292226, 12455070307287959, 17390530055093252, 16576085708249149, 17427762961292226, 21392296981267440,
    11718104713114918, 30040178091637078, 17390530055093252, 12455070307287959, 11718104713114918, 12455070307287959,
    16399928753095501, 16576085708249149, 25311456927755590, 25255159313493463, 28720746778477398, 14068862231259659,
    13893775524460172, 19442411018381434, 17565288057379027, 27720747257863593, 19442411018381434, 14068862231259659,
    14068862231259659, 12846469809823008, 14068862231259659, 17565288057379027, 12846469809823008, 24255154017686184,
    13893775524460172, 6228818690495880, 10553629293916271, 11300924490976300, 11241387363998936
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    25468845530831019, 1584962500724866, 9202123823830461, 10133142212400602, 9202123823830461
  ]

abbrev PositiveTerm := Fin 59
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 24950343217 / 250000000000
noncomputable def negativeCeiling : ℝ := 8015226487 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 428327725017733122836398080, coefficient := (-428327725017733122836398080) }, { argument := 136589352174591718011269770379264, coefficient := 136589352174591718011269770379264 }, { argument := 175443092835661281549531217920, coefficient := 175443092835661281549531217920 }, { argument := 599851821168247282459207532544, coefficient := 599851821168247282459207532544 }, { argument := 175443036167263487113788653568, coefficient := 175443036167263487113788653568 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 631318002131333408448946634752, coefficient := 631318002131333408448946634752 }, { argument := 89092997202319711659146346496, coefficient := 89092997202319711659146346496 }, { argument := 18980319209676856158175132385280, coefficient := 18980319209676856158175132385280 }, { argument := 2204577781836123928927387254784, coefficient := 2204577781836123928927387254784 }, { argument := 70137040350762326199753506816, coefficient := 70137040350762326199753506816 }, { argument := 18980328484404628514158332084224, coefficient := 18980328484404628514158332084224 }, { argument := 72032636035918064745692790784, coefficient := 72032636035918064745692790784 }, { argument := 72032636035918064745692790784, coefficient := 72032636035918064745692790784 }, { argument := 1218868025555139885038959591424, coefficient := 1218868025555139885038959591424 }, { argument := 66345848980450849107874938880, coefficient := 66345848980450849107874938880 }, { argument := 2204577781836123928927387254784, coefficient := 2204577781836123928927387254784 }, { argument := 1218868025555139885038959591424, coefficient := 1218868025555139885038959591424 }, { argument := 631313364767447230457346785280, coefficient := 631313364767447230457346785280 }, { argument := 70137040350762326199753506816, coefficient := 70137040350762326199753506816 }, { argument := 66345848980450849107874938880, coefficient := 66345848980450849107874938880 }, { argument := 89092997202319711659146346496, coefficient := 89092997202319711659146346496 }, { argument := 46665387720901694842597386747904, coefficient := (-46665387720901694842597386747904) }, { argument := 196638003916977374588705964032, coefficient := 196638003916977374588705964032 }, { argument := 10427594714740487099818144956416, coefficient := 10427594714740487099818144956416 }, { argument := 3323462806405855522701447266304, coefficient := 3323462806405855522701447266304 }, { argument := 75045062728729978318872211619840, coefficient := 75045062728729978318872211619840 }, { argument := 3410350722913198150745929547776, coefficient := 3410350722913198150745929547776 }, { argument := 108609895634178285055602851840, coefficient := 108609895634178285055602851840 }, { argument := 3323462806405855522701447266304, coefficient := 3323462806405855522701447266304 }, { argument := 1889812184034702159967489622016, coefficient := 1889812184034702159967489622016 }, { argument := 3410350722913198150745929547776, coefficient := 3410350722913198150745929547776 }, { argument := 53240570839874195334256517971968, coefficient := 53240570839874195334256517971968 }, { argument := 2085309996176223073067574755328, coefficient := 2085309996176223073067574755328 }, { argument := 10427600017958047362429719937024, coefficient := 10427600017958047362429719937024 }, { argument := 3323462806405855522701447266304, coefficient := 3323462806405855522701447266304 }, { argument := 108609895634178285055602851840, coefficient := 108609895634178285055602851840 }, { argument := 2085309996176223073067574755328, coefficient := 2085309996176223073067574755328 }, { argument := 108609895634178285055602851840, coefficient := 108609895634178285055602851840 }, { argument := 3345184785532691179712567836672, coefficient := 3345184785532691179712567836672 }, { argument := 1889812184034702159967489622016, coefficient := 1889812184034702159967489622016 }, { argument := 196638003916977374588705964032, coefficient := 196638003916977374588705964032 }, { argument := 177946453007037702235099712454656, coefficient := (-177946453007037702235099712454656) }, { argument := 378224956937616341866643456000, coefficient := 378224956937616341866643456000 }, { argument := 4178264814222705602767922135040, coefficient := 4178264814222705602767922135040 }, { argument := 332406243361238437877210152960, coefficient := 332406243361238437877210152960 }, { argument := 294416958405668330691243278336, coefficient := 294416958405668330691243278336 }, { argument := 13780613117633056381709483769856, coefficient := 13780613117633056381709483769856 }, { argument := 3751441889362548084614228869120, coefficient := 3751441889362548084614228869120 }, { argument := 4178266202598451566443614961664, coefficient := 4178266202598451566443614961664 }, { argument := 13780613117633056381709483769856, coefficient := 13780613117633056381709483769856 }, { argument := 332406243361238437877210152960, coefficient := 332406243361238437877210152960 }, { argument := 332406243361238437877210152960, coefficient := 332406243361238437877210152960 }, { argument := 284919637166775803894751559680, coefficient := 284919637166775803894751559680 }, { argument := 332406243361238437877210152960, coefficient := 332406243361238437877210152960 }, { argument := 3751441889362548084614228869120, coefficient := 3751441889362548084614228869120 }, { argument := 284919637166775803894751559680, coefficient := 284919637166775803894751559680 }, { argument := 378223568561870378190950629376, coefficient := 378223568561870378190950629376 }, { argument := 294416958405668330691243278336, coefficient := 294416958405668330691243278336 }, { argument := 46665387720901694842597386747904, coefficient := (-46665387720901694842597386747904) }, { argument := 5802843934150220038589644800, coefficient := 5802843934150220038589644800 }, { argument := 116288992440370409573336481792, coefficient := 116288992440370409573336481792 }, { argument := 195207669944813402098155651072, coefficient := 195207669944813402098155651072 }, { argument := 187315802194369102845673734144, coefficient := 187315802194369102845673734144 }] }

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

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-54783024786010665322714031456256)
def positiveArguments : Array ℕ := #[
    75, 2421, 1617, 39, 1503, 9
  ]
def positiveCoefficients : Array ℕ := #[
    5802843934150220038589644800, 187315802194369102845673734144, 125109315220278744031992741888, 6034957691516228840133230592, 116288992440370409573336481792, 5570730176784211237046059008
  ]
def positiveScales : Array ℕ := #[
    6, 11, 10, 5, 10, 3
  ]
def negativeArguments : Array ℕ := #[
    3
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6228818690495880, 11241387363998936, 10659103963471994, 5285402218862248, 10553629293916271, 3169925001442312
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 1
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
noncomputable def positiveFloor : ℝ := 572027 / 10000000000
noncomputable def negativeCeiling : ℝ := 18138457 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5802843934150220038589644800, coefficient := 5802843934150220038589644800 }, { argument := 187315802194369102845673734144, coefficient := 187315802194369102845673734144 }, { argument := 125109315220278744031992741888, coefficient := 125109315220278744031992741888 }, { argument := 6034957691516228840133230592, coefficient := 6034957691516228840133230592 }, { argument := 116288992440370409573336481792, coefficient := 116288992440370409573336481792 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end TermShard8


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
