import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 9, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9

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
def constantNumerator : ℤ := (-15934021139833062504732337916346368)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    38673649, 2205, 2765354575, 24885, 2205, 2765354267,
    2205, 2205, 91413, 567, 24885, 91413,
    19336877, 2205, 567, 2205, 17955643323830513, 130283486379,
    3380609427, 65154070348058945, 209857831353, 8979406952775399, 209857831353, 218699425239,
    130283486379, 6501171975, 9021680517612295, 1603690855, 9021684908883193, 1603690855,
    1603690855, 5768428315, 801845695, 121878100161, 121878071103, 9858317,
    3162505593, 3162504839, 1085, 17955652040208143, 130283455317, 3380608621,
    65154101626842815, 209857781319, 8979411311935769, 209857781319, 218699373097, 130283455317,
    6501170425, 16362754250397039, 5768428315, 16362762130483857, 5768428315, 2830694345,
    196318616427, 196318569621, 12245, 1085, 9023263518376475, 801845695,
    9023267910630885, 801845695, 2830694031, 1085
  ]
def negativeCoefficients : Array ℕ := #[
    365262287615730343498018193408, 42650902916004117283633889280, 13059017758230232520321086259200, 481345904337760752201011036160, 42650902916004117283633889280, 13059016303741355796470360440832,
    42650902916004117283633889280, 42650902916004117283633889280, 1768184575174913547958650667008, 43869500142175663491737714688, 481345904337760752201011036160, 1768184575174913547958650667008,
    365263279312691746123513069568, 42650902916004117283633889280, 43869500142175663491737714688, 42650902916004117283633889280, 10108128572800079073365570093056, 150206633141502333747833339904,
    7795154614129861631624085504, 36678480867648668415460995235840, 241949606677030705258486038528, 10109913451631831977387911806976, 241949606677030705258486038528, 252143270403200524315225227264,
    150206633141502333747833339904, 7495340975124866953484697600, 10157509254343598809416812462080, 29582874775533453852729671680, 10157514198475093788342649618432, 29582874775533453852729671680,
    29582874775533453852729671680, 106408720834344624627688407040, 29582884644541533287339786240, 140515882616244118667327963136, 140515849114651037801568534528, 372436686226432257553183277056,
    7292241413218257655390273536, 7292239674612628708265033728, 41973904457019924945798430720, 10108133479684459884431452143616, 150206597329454557649952571392, 7795152755620396205386760192,
    36678498476038591107246095073280, 241949548991756143759504441344, 10109918359610086472446279417856, 241949548991756143759504441344, 252143210287567431105010204672, 150206597329454557649952571392,
    7495339188096534812871884800, 36845646972421552220529777180672, 106408720834344624627688407040, 36845664716799580816508543041536, 106408720834344624627688407040, 13367576098076644078565583749120,
    226339954633351304919228874752, 226339900669707360291149316096, 473705493157796295816868003840, 41973904457019924945798430720, 10159291554756520874019808870400, 29582884644541533287339786240,
    10159296499995351922124248842240, 29582884644541533287339786240, 13367574615253568457496986648576, 41973904457019924945798430720
  ]
def negativeScales : Array ℕ := #[
    25, 11, 31, 14, 11, 31,
    11, 11, 16, 9, 14, 16,
    24, 11, 9, 11, 53, 36,
    31, 55, 37, 52, 37, 37,
    36, 32, 53, 30, 53, 30,
    30, 32, 29, 36, 36, 23,
    31, 31, 10, 53, 36, 31,
    55, 37, 52, 37, 37, 36,
    32, 53, 32, 53, 32, 31,
    37, 37, 13, 10, 53, 29,
    53, 29, 31, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25204847558599647, 11106562940444883, 31364817329309735, 14602988766570523, 11106562940444883, 31364817168625061,
    11106562940444883, 11106562940444883, 16480111727566799, 9147204924942229, 14602988766570523, 16480111727566799,
    24204851475550273, 11106562940444883, 9147204924942229, 11106562940444883, 53995286883688780, 36922863282108176,
    31654636200534571, 55854704830697196, 37610621345654863, 52995541610308774, 37610621345654863, 37670158472659953,
    36922863282108176, 32598052672149598, 53002317620494122, 30578748912899555, 53002318322720630, 30578748912899555,
    30578748912899555, 32425531144949343, 29578749394190395, 36826647961407063, 36826647617441753, 23232909941789491,
    31558420885253018, 31558420541287716, 10083479327331842, 53995287584029944, 36922862938142835, 31654635856569269,
    55854705523297627, 37610621001689561, 52995542310682393, 37610621001689561, 37670158128694651, 36922862938142835,
    32598052328184297, 53861265129804464, 32425531144949343, 53861265824587245, 32425531144949343, 31398508831149600,
    37514406030388429, 37514405686423127, 13579905153454551, 10083479327331842, 53002570742626671, 29578749394190395,
    53002571444887234, 29578749394190395, 31398508671115978, 10083479327331842
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
noncomputable def negativeCeiling : ℝ := 6872837661 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 365262287615730343498018193408, coefficient := (-365262287615730343498018193408) }, { argument := 42650902916004117283633889280, coefficient := (-42650902916004117283633889280) }, { argument := 13059017758230232520321086259200, coefficient := (-13059017758230232520321086259200) }, { argument := 481345904337760752201011036160, coefficient := (-481345904337760752201011036160) }, { argument := 42650902916004117283633889280, coefficient := (-42650902916004117283633889280) }, { argument := 13059016303741355796470360440832, coefficient := (-13059016303741355796470360440832) }, { argument := 42650902916004117283633889280, coefficient := (-42650902916004117283633889280) }, { argument := 42650902916004117283633889280, coefficient := (-42650902916004117283633889280) }, { argument := 1768184575174913547958650667008, coefficient := (-1768184575174913547958650667008) }, { argument := 43869500142175663491737714688, coefficient := (-43869500142175663491737714688) }, { argument := 481345904337760752201011036160, coefficient := (-481345904337760752201011036160) }, { argument := 1768184575174913547958650667008, coefficient := (-1768184575174913547958650667008) }, { argument := 365263279312691746123513069568, coefficient := (-365263279312691746123513069568) }, { argument := 42650902916004117283633889280, coefficient := (-42650902916004117283633889280) }, { argument := 43869500142175663491737714688, coefficient := (-43869500142175663491737714688) }, { argument := 42650902916004117283633889280, coefficient := (-42650902916004117283633889280) }, { argument := 10108128572800079073365570093056, coefficient := (-10108128572800079073365570093056) }, { argument := 150206633141502333747833339904, coefficient := (-150206633141502333747833339904) }, { argument := 7795154614129861631624085504, coefficient := (-7795154614129861631624085504) }, { argument := 36678480867648668415460995235840, coefficient := (-36678480867648668415460995235840) }, { argument := 241949606677030705258486038528, coefficient := (-241949606677030705258486038528) }, { argument := 10109913451631831977387911806976, coefficient := (-10109913451631831977387911806976) }, { argument := 241949606677030705258486038528, coefficient := (-241949606677030705258486038528) }, { argument := 252143270403200524315225227264, coefficient := (-252143270403200524315225227264) }, { argument := 150206633141502333747833339904, coefficient := (-150206633141502333747833339904) }, { argument := 7495340975124866953484697600, coefficient := (-7495340975124866953484697600) }, { argument := 10157509254343598809416812462080, coefficient := (-10157509254343598809416812462080) }, { argument := 29582874775533453852729671680, coefficient := (-29582874775533453852729671680) }, { argument := 10157514198475093788342649618432, coefficient := (-10157514198475093788342649618432) }, { argument := 29582874775533453852729671680, coefficient := (-29582874775533453852729671680) }, { argument := 29582874775533453852729671680, coefficient := (-29582874775533453852729671680) }, { argument := 106408720834344624627688407040, coefficient := (-106408720834344624627688407040) }, { argument := 29582884644541533287339786240, coefficient := (-29582884644541533287339786240) }, { argument := 140515882616244118667327963136, coefficient := (-140515882616244118667327963136) }, { argument := 140515849114651037801568534528, coefficient := (-140515849114651037801568534528) }, { argument := 372436686226432257553183277056, coefficient := (-372436686226432257553183277056) }, { argument := 7292241413218257655390273536, coefficient := (-7292241413218257655390273536) }, { argument := 7292239674612628708265033728, coefficient := (-7292239674612628708265033728) }, { argument := 41973904457019924945798430720, coefficient := (-41973904457019924945798430720) }, { argument := 10108133479684459884431452143616, coefficient := (-10108133479684459884431452143616) }, { argument := 150206597329454557649952571392, coefficient := (-150206597329454557649952571392) }, { argument := 7795152755620396205386760192, coefficient := (-7795152755620396205386760192) }, { argument := 36678498476038591107246095073280, coefficient := (-36678498476038591107246095073280) }, { argument := 241949548991756143759504441344, coefficient := (-241949548991756143759504441344) }, { argument := 10109918359610086472446279417856, coefficient := (-10109918359610086472446279417856) }, { argument := 241949548991756143759504441344, coefficient := (-241949548991756143759504441344) }, { argument := 252143210287567431105010204672, coefficient := (-252143210287567431105010204672) }, { argument := 150206597329454557649952571392, coefficient := (-150206597329454557649952571392) }, { argument := 7495339188096534812871884800, coefficient := (-7495339188096534812871884800) }, { argument := 36845646972421552220529777180672, coefficient := (-36845646972421552220529777180672) }, { argument := 106408720834344624627688407040, coefficient := (-106408720834344624627688407040) }, { argument := 36845664716799580816508543041536, coefficient := (-36845664716799580816508543041536) }, { argument := 106408720834344624627688407040, coefficient := (-106408720834344624627688407040) }, { argument := 13367576098076644078565583749120, coefficient := (-13367576098076644078565583749120) }, { argument := 226339954633351304919228874752, coefficient := (-226339954633351304919228874752) }, { argument := 226339900669707360291149316096, coefficient := (-226339900669707360291149316096) }, { argument := 473705493157796295816868003840, coefficient := (-473705493157796295816868003840) }, { argument := 41973904457019924945798430720, coefficient := (-41973904457019924945798430720) }, { argument := 10159291554756520874019808870400, coefficient := (-10159291554756520874019808870400) }, { argument := 29582884644541533287339786240, coefficient := (-29582884644541533287339786240) }, { argument := 10159296499995351922124248842240, coefficient := (-10159296499995351922124248842240) }, { argument := 29582884644541533287339786240, coefficient := (-29582884644541533287339786240) }, { argument := 13367574615253568457496986648576, coefficient := (-13367574615253568457496986648576) }, { argument := 41973904457019924945798430720, coefficient := (-41973904457019924945798430720) }] }

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
def constantNumerator : ℤ := 40206741260789992994863743200395264
def positiveArguments : Array ℕ := #[
    1873, 3, 489, 535, 489, 535,
    45, 7515, 195, 8085, 12105, 375,
    12105, 12615, 7515, 375, 3875, 4375,
    1875, 49375, 4375, 1875, 4375, 4375,
    181375, 1125, 49375, 181375, 3875, 4375,
    1125, 4375, 801, 12259947703, 12259953481, 1075249123,
    971761059, 1075407249
  ]
def positiveCoefficients : Array ℕ := #[
    296788696778434208625415637958656, 475368975085586025561263702016, 302676339605275477212835872768, 331148960508839223535515729920, 302676339605275477212835872768, 331148960508839223535515729920,
    27853650883921056185230295040, 581444962201852047866682408960, 30174788457581144200666152960, 625546576101393720159963709440, 936579010971845514228368670720, 29014219670751100192948224000,
    936579010971845514228368670720, 976038349724067010490778255360, 581444962201852047866682408960, 29014219670751100192948224000, 74953400816107008831782912000, 84624807373024042229432320000,
    72535549176877750482370560000, 955051397495557048017879040000, 84624807373024042229432320000, 72535549176877750482370560000, 84624807373024042229432320000, 84624807373024042229432320000,
    3508302728521653864997322752000, 87042659012253300578844672000, 955051397495557048017879040000, 3508302728521653864997322752000, 74953400816107008831782912000, 84624807373024042229432320000,
    87042659012253300578844672000, 84624807373024042229432320000, 63461758173925734412428704219136, 115791932228763791372154438680576, 115791986800430867413774528151552, 40621763353521444314782172708864,
    146848379340144377338096200450048, 40627737184901206278934659858432
  ]
def positiveScales : Array ℕ := #[
    10, 1, 8, 9, 8, 9,
    5, 12, 7, 12, 13, 8,
    13, 13, 12, 8, 11, 12,
    10, 15, 12, 10, 12, 12,
    17, 10, 15, 17, 11, 12,
    10, 12, 9, 33, 33, 30,
    29, 30
  ]
def negativeArguments : Array ℕ := #[
    1603690855, 5768428315, 801845695, 196318616427, 196318569621, 1085,
    204589784901, 204589736123, 44981, 279, 121878100161, 121878071103,
    12245, 44981, 1232293, 6081741525, 6081740075, 1085,
    279, 1085, 3, 1, 15, 125,
    801, 2923
  ]
def negativeCoefficients : Array ℕ := #[
    29582874775533453852729671680, 106408720834344624627688407040, 29582884644541533287339786240, 226339954633351304919228874752, 226339900669707360291149316096, 41973904457019924945798430720,
    235875962635252103391662309376, 235875906398046951678880514048, 1740118153346740317038672084992, 43173158870077637087106957312, 140515882616244118667327963136, 140515849114651037801568534528,
    473705493157796295816868003840, 1740118153346740317038672084992, 372437706257592557396549435392, 7011770589632940053259878400, 7011768917896758373331763200, 41973904457019924945798430720,
    43173158870077637087106957312, 41973904457019924945798430720, 475368975085586025561263702016, 1267650600228229401496703205376, 4753689750855860255612637020160, 9903520314283042199192993792000,
    63461758173925734412428704219136, 231583919029194658785928966832128
  ]
def negativeScales : Array ℕ := #[
    30, 32, 29, 37, 37, 10,
    37, 37, 15, 8, 36, 36,
    13, 15, 20, 32, 32, 10,
    8, 10, 1, 0, 3, 6,
    9, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10871135184083522, 1584962500720924, 8933690654464738, 9063395081288509, 8933690654464738, 9063395081288509,
    5491853096329661, 12875557388630600, 7607330313749179, 12981032057285308, 13563315458886175, 8550746785383158,
    13563315458886175, 13622852585863008, 12875557388630600, 8550746785383158, 11919980594664560, 12095067301607053,
    10872674880106463, 15591493127726274, 12095067301607053, 10872674880106463, 12095067301607053, 12095067301607053,
    17468616088728825, 10135709286104399, 15591493127726274, 17468616088728825, 11919980594664560, 12095067301607053,
    10135709286104399, 12095067301607053, 9645658432407524, 33513233773841649, 33513234453770322, 30002023808571249,
    29856026380039366, 30002235955522679
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30578748912899555, 32425531144949343, 29578749394190395, 37514406030388429, 37514405686423127, 10083479327331842,
    37573943157368061, 37573942813402759, 15457028114453680, 8124121311829188, 36826647961407063, 36826647617441753,
    13579905153454551, 15457028114453680, 20232913893043317, 32501837356885226, 32501837012919924, 10083479327331842,
    8124121311829188, 10083479327331842, 1584962500724866, 0, 3906890600547867, 6965784298236803,
    9645658432427781, 11513234113806472
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 112306476083 / 500000000000
noncomputable def negativeCeiling : ℝ := 41975621823 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 29582874775533453852729671680, coefficient := (-29582874775533453852729671680) }, { argument := 106408720834344624627688407040, coefficient := (-106408720834344624627688407040) }, { argument := 29582884644541533287339786240, coefficient := (-29582884644541533287339786240) }, { argument := 226339954633351304919228874752, coefficient := (-226339954633351304919228874752) }, { argument := 226339900669707360291149316096, coefficient := (-226339900669707360291149316096) }, { argument := 41973904457019924945798430720, coefficient := (-41973904457019924945798430720) }, { argument := 235875962635252103391662309376, coefficient := (-235875962635252103391662309376) }, { argument := 235875906398046951678880514048, coefficient := (-235875906398046951678880514048) }, { argument := 1740118153346740317038672084992, coefficient := (-1740118153346740317038672084992) }, { argument := 43173158870077637087106957312, coefficient := (-43173158870077637087106957312) }, { argument := 140515882616244118667327963136, coefficient := (-140515882616244118667327963136) }, { argument := 140515849114651037801568534528, coefficient := (-140515849114651037801568534528) }, { argument := 473705493157796295816868003840, coefficient := (-473705493157796295816868003840) }, { argument := 1740118153346740317038672084992, coefficient := (-1740118153346740317038672084992) }, { argument := 372437706257592557396549435392, coefficient := (-372437706257592557396549435392) }, { argument := 7011770589632940053259878400, coefficient := (-7011770589632940053259878400) }, { argument := 7011768917896758373331763200, coefficient := (-7011768917896758373331763200) }, { argument := 41973904457019924945798430720, coefficient := (-41973904457019924945798430720) }, { argument := 43173158870077637087106957312, coefficient := (-43173158870077637087106957312) }, { argument := 41973904457019924945798430720, coefficient := (-41973904457019924945798430720) }, { argument := 296788696778434208625415637958656, coefficient := 296788696778434208625415637958656 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 27853650883921056185230295040, coefficient := 27853650883921056185230295040 }, { argument := 581444962201852047866682408960, coefficient := 581444962201852047866682408960 }, { argument := 30174788457581144200666152960, coefficient := 30174788457581144200666152960 }, { argument := 625546576101393720159963709440, coefficient := 625546576101393720159963709440 }, { argument := 936579010971845514228368670720, coefficient := 936579010971845514228368670720 }, { argument := 29014219670751100192948224000, coefficient := 29014219670751100192948224000 }, { argument := 936579010971845514228368670720, coefficient := 936579010971845514228368670720 }, { argument := 976038349724067010490778255360, coefficient := 976038349724067010490778255360 }, { argument := 581444962201852047866682408960, coefficient := 581444962201852047866682408960 }, { argument := 29014219670751100192948224000, coefficient := 29014219670751100192948224000 }, { argument := 4753689750855860255612637020160, coefficient := (-4753689750855860255612637020160) }, { argument := 74953400816107008831782912000, coefficient := 74953400816107008831782912000 }, { argument := 84624807373024042229432320000, coefficient := 84624807373024042229432320000 }, { argument := 72535549176877750482370560000, coefficient := 72535549176877750482370560000 }, { argument := 955051397495557048017879040000, coefficient := 955051397495557048017879040000 }, { argument := 84624807373024042229432320000, coefficient := 84624807373024042229432320000 }, { argument := 72535549176877750482370560000, coefficient := 72535549176877750482370560000 }, { argument := 84624807373024042229432320000, coefficient := 84624807373024042229432320000 }, { argument := 84624807373024042229432320000, coefficient := 84624807373024042229432320000 }, { argument := 3508302728521653864997322752000, coefficient := 3508302728521653864997322752000 }, { argument := 87042659012253300578844672000, coefficient := 87042659012253300578844672000 }, { argument := 955051397495557048017879040000, coefficient := 955051397495557048017879040000 }, { argument := 3508302728521653864997322752000, coefficient := 3508302728521653864997322752000 }, { argument := 74953400816107008831782912000, coefficient := 74953400816107008831782912000 }, { argument := 84624807373024042229432320000, coefficient := 84624807373024042229432320000 }, { argument := 87042659012253300578844672000, coefficient := 87042659012253300578844672000 }, { argument := 84624807373024042229432320000, coefficient := 84624807373024042229432320000 }, { argument := 9903520314283042199192993792000, coefficient := (-9903520314283042199192993792000) }, { argument := 63461758173925734412428704219136, coefficient := 63461758173925734412428704219136 }, { argument := 63461758173925734412428704219136, coefficient := (-63461758173925734412428704219136) }, { argument := 115791932228763791372154438680576, coefficient := 115791932228763791372154438680576 }, { argument := 115791986800430867413774528151552, coefficient := 115791986800430867413774528151552 }, { argument := 231583919029194658785928966832128, coefficient := (-231583919029194658785928966832128) }, { argument := 40621763353521444314782172708864, coefficient := 40621763353521444314782172708864 }, { argument := 146848379340144377338096200450048, coefficient := 146848379340144377338096200450048 }, { argument := 40627737184901206278934659858432, coefficient := 40627737184901206278934659858432 }] }

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

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-23140832168176899184193681670275072)
def positiveArguments : Array ℕ := #[
    70170917, 697586115, 2790344149, 35085565
  ]
def positiveCoefficients : Array ℕ := #[
    662745573026055592219418558464, 26354058307129998848404299448320, 26354055369818046503484976529408, 662747584754177294688279592960
  ]
def positiveScales : Array ℕ := #[
    26, 29, 31, 25
  ]
def negativeArguments : Array ℕ := #[
    2879, 341
  ]
def negativeCoefficients : Array ℕ := #[
    228097879878567027931813033017344, 54033606834728278238796974129152
  ]
def negativeScales : Array ℕ := #[
    11, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    26064369880017763, 29377796083588735, 31377795922792034, 25064374259233405
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11491352073563637, 8413627929024184
  ]

abbrev PositiveTerm := Fin 4
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 19681098821 / 1000000000000
noncomputable def negativeCeiling : ℝ := 18511627611 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 228097879878567027931813033017344, coefficient := (-228097879878567027931813033017344) }, { argument := 662745573026055592219418558464, coefficient := 662745573026055592219418558464 }, { argument := 26354058307129998848404299448320, coefficient := 26354058307129998848404299448320 }, { argument := 26354055369818046503484976529408, coefficient := 26354055369818046503484976529408 }, { argument := 662747584754177294688279592960, coefficient := 662747584754177294688279592960 }, { argument := 54033606834728278238796974129152, coefficient := (-54033606834728278238796974129152) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9
