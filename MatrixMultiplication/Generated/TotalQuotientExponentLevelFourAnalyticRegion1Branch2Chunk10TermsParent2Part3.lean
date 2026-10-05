import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 10, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-11504011950103796518393041500766208)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    279, 590955745213, 2817, 324779503683, 5643, 2529,
    855, 279, 524403151, 19365510705, 154924047703, 4195263145,
    5070568511373, 320055, 104439, 9228609640563, 1054497, 5070568511373,
    2112363, 946689, 320055, 104439, 4870547561715, 4870538928909,
    6207421725, 12825, 4185, 11306983395, 42255, 6207421725,
    84645, 37935, 12825, 4185, 676750464885, 676743047307,
    3507, 360826349766393, 608106915, 6497155930806321, 15047411535, 478722465,
    25988216434977159, 245830455, 245830455, 8319420135, 452845575, 15047411535,
    8319420135, 722061245310915, 478722465, 452845575, 608106915, 766630121260297,
    5985, 1953, 42061513197064453, 19719, 12266081806196331, 39501,
    17703, 5985, 1953, 9424913517129
  ]
def negativeCoefficients : Array ℕ := #[
    84322575918120384935755776, 2725302347708129869137342103552, 1702772016927205192573648896, 748890548103338717817618825216, 1705492100021338108216737792, 1528686698902698591415959552,
    2067263151541015888747560960, 84322575918120384935755776, 38694122871775460504910168064, 1428922479327270523521592197120, 1428922129420205561361962369024, 38694472778840422664539996160,
    11691934954688518865439053316096, 48365344149595017563823144960, 1972796932417691505892786176, 42559450048908588879248413949952, 39837770312692738151254327296, 11691934954688518865439053316096,
    39901408923415889490154094592, 35764899226411052461669220352, 48365344149595017563823144960, 1972796932417691505892786176, 5615359023111667678650921123840, 5615349070163985179634705629184,
    458026879674638688164669030400, 3876118409139404791401676800, 158104829846475721754542080, 1668616231465988449400059330560, 3192697531738509736075591680, 458026879674638688164669030400,
    3197797687540008952906383360, 2866287560442559858904924160, 3876118409139404791401676800, 158104829846475721754542080, 1560480328437194720324112875520, 1560463224666818123030555787264,
    67835245590216072251112947712, 406254353588345942804615135232, 2804398157614512009809756160, 14630294514473677674291142852608, 69393937389482499306569072640, 2207717698547594560914063360,
    14630065231573366657776623812608, 2267385744454286305803632640, 2267385744454286305803632640, 38366553518002791963993047040, 2088381606734211071134924800, 69393937389482499306569072640,
    38366553518002791963993047040, 406484344415114137021427220480, 2207717698547594560914063360, 2088381606734211071134924800, 2804398157614512009809756160, 13810380513755486930062695989248,
    1808855257598388902654115840, 73782253928355336818786304, 47357053790234667604804655644672, 1489925514811304543501942784, 13810380362920454206309263212544, 1492305587518670844689645568,
    1337600861539861267488964608, 1808855257598388902654115840, 73782253928355336818786304, 10866185472957776708947257851904
  ]
def negativeScales : Array ℕ := #[
    8, 39, 11, 38, 12, 11,
    9, 8, 28, 34, 37, 31,
    42, 18, 16, 43, 20, 42,
    21, 19, 18, 16, 42, 42,
    32, 13, 12, 33, 15, 32,
    16, 15, 13, 12, 39, 39,
    11, 48, 29, 52, 33, 28,
    54, 27, 27, 32, 28, 33,
    32, 49, 28, 28, 29, 49,
    12, 10, 55, 14, 53, 15,
    14, 12, 10, 43
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    8124121311829188, 39104259139388332, 11459943848374998, 38240669632971488, 12462246634244425, 11304351321663239,
    9739780609952834, 8124121311829188, 28966101127104179, 34172770497327696, 37172770144048035, 31966114173194429,
    42205284649694931, 18287960321452706, 16672301023545835, 43069250450034401, 20008123560054376, 42205284649694931,
    21010426345923797, 19852531035160402, 18287960321452706, 16672301023545835, 42147221112221683, 42147218555113415,
    32531347018256009, 13646671205401350, 12031011907437707, 33396495031024919, 15366834443983451, 32531347018256009,
    16369137229852872, 15211241917271758, 13646671205401350, 12031011907437707, 39299833017242310, 39299817204380409,
    11776021715645854, 48358298025356825, 29179749754116540, 52528729753384089, 33808796284684230, 28834614269355388,
    54528707143593497, 27873088418556653, 27873088418556653, 32953835840886814, 28754443919631609, 33808796284684230,
    32953835840886814, 49359114540270906, 28834614269355388, 28754443919631609, 29179749754116540, 49445524011846106,
    12547135531832084, 10931476241484805, 55223350271325770, 14267298770432535, 53445523996089193, 15269601556301956,
    14111706243720843, 12547135531832084, 10931476241484805, 43099616518941423
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
noncomputable def negativeCeiling : ℝ := 118741176099 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2725302347708129869137342103552, coefficient := (-2725302347708129869137342103552) }, { argument := 1702772016927205192573648896, coefficient := (-1702772016927205192573648896) }, { argument := 748890548103338717817618825216, coefficient := (-748890548103338717817618825216) }, { argument := 1705492100021338108216737792, coefficient := (-1705492100021338108216737792) }, { argument := 1528686698902698591415959552, coefficient := (-1528686698902698591415959552) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 38694122871775460504910168064, coefficient := (-38694122871775460504910168064) }, { argument := 1428922479327270523521592197120, coefficient := (-1428922479327270523521592197120) }, { argument := 1428922129420205561361962369024, coefficient := (-1428922129420205561361962369024) }, { argument := 38694472778840422664539996160, coefficient := (-38694472778840422664539996160) }, { argument := 11691934954688518865439053316096, coefficient := (-11691934954688518865439053316096) }, { argument := 48365344149595017563823144960, coefficient := (-48365344149595017563823144960) }, { argument := 1972796932417691505892786176, coefficient := (-1972796932417691505892786176) }, { argument := 42559450048908588879248413949952, coefficient := (-42559450048908588879248413949952) }, { argument := 39837770312692738151254327296, coefficient := (-39837770312692738151254327296) }, { argument := 11691934954688518865439053316096, coefficient := (-11691934954688518865439053316096) }, { argument := 39901408923415889490154094592, coefficient := (-39901408923415889490154094592) }, { argument := 35764899226411052461669220352, coefficient := (-35764899226411052461669220352) }, { argument := 48365344149595017563823144960, coefficient := (-48365344149595017563823144960) }, { argument := 1972796932417691505892786176, coefficient := (-1972796932417691505892786176) }, { argument := 5615359023111667678650921123840, coefficient := (-5615359023111667678650921123840) }, { argument := 5615349070163985179634705629184, coefficient := (-5615349070163985179634705629184) }, { argument := 458026879674638688164669030400, coefficient := (-458026879674638688164669030400) }, { argument := 3876118409139404791401676800, coefficient := (-3876118409139404791401676800) }, { argument := 158104829846475721754542080, coefficient := (-158104829846475721754542080) }, { argument := 1668616231465988449400059330560, coefficient := (-1668616231465988449400059330560) }, { argument := 3192697531738509736075591680, coefficient := (-3192697531738509736075591680) }, { argument := 458026879674638688164669030400, coefficient := (-458026879674638688164669030400) }, { argument := 3197797687540008952906383360, coefficient := (-3197797687540008952906383360) }, { argument := 2866287560442559858904924160, coefficient := (-2866287560442559858904924160) }, { argument := 3876118409139404791401676800, coefficient := (-3876118409139404791401676800) }, { argument := 158104829846475721754542080, coefficient := (-158104829846475721754542080) }, { argument := 1560480328437194720324112875520, coefficient := (-1560480328437194720324112875520) }, { argument := 1560463224666818123030555787264, coefficient := (-1560463224666818123030555787264) }, { argument := 67835245590216072251112947712, coefficient := (-67835245590216072251112947712) }, { argument := 406254353588345942804615135232, coefficient := (-406254353588345942804615135232) }, { argument := 2804398157614512009809756160, coefficient := (-2804398157614512009809756160) }, { argument := 14630294514473677674291142852608, coefficient := (-14630294514473677674291142852608) }, { argument := 69393937389482499306569072640, coefficient := (-69393937389482499306569072640) }, { argument := 2207717698547594560914063360, coefficient := (-2207717698547594560914063360) }, { argument := 14630065231573366657776623812608, coefficient := (-14630065231573366657776623812608) }, { argument := 2267385744454286305803632640, coefficient := (-2267385744454286305803632640) }, { argument := 2267385744454286305803632640, coefficient := (-2267385744454286305803632640) }, { argument := 38366553518002791963993047040, coefficient := (-38366553518002791963993047040) }, { argument := 2088381606734211071134924800, coefficient := (-2088381606734211071134924800) }, { argument := 69393937389482499306569072640, coefficient := (-69393937389482499306569072640) }, { argument := 38366553518002791963993047040, coefficient := (-38366553518002791963993047040) }, { argument := 406484344415114137021427220480, coefficient := (-406484344415114137021427220480) }, { argument := 2207717698547594560914063360, coefficient := (-2207717698547594560914063360) }, { argument := 2088381606734211071134924800, coefficient := (-2088381606734211071134924800) }, { argument := 2804398157614512009809756160, coefficient := (-2804398157614512009809756160) }, { argument := 13810380513755486930062695989248, coefficient := (-13810380513755486930062695989248) }, { argument := 1808855257598388902654115840, coefficient := (-1808855257598388902654115840) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 47357053790234667604804655644672, coefficient := (-47357053790234667604804655644672) }, { argument := 1489925514811304543501942784, coefficient := (-1489925514811304543501942784) }, { argument := 13810380362920454206309263212544, coefficient := (-13810380362920454206309263212544) }, { argument := 1492305587518670844689645568, coefficient := (-1492305587518670844689645568) }, { argument := 1337600861539861267488964608, coefficient := (-1337600861539861267488964608) }, { argument := 1808855257598388902654115840, coefficient := (-1808855257598388902654115840) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 10866185472957776708947257851904, coefficient := (-10866185472957776708947257851904) }] }

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


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1832838598531366651415466654826496)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    9424913061303, 316538558151, 25935, 8463, 576245700921, 85449,
    316538558151, 171171, 76713, 25935, 8463, 4870547561715,
    4870538928909, 32915423, 59076899625, 59076644055, 5649, 465,
    1953, 8463, 279, 279, 651, 8463,
    8463, 279, 104439, 4185, 1953, 8463,
    651, 4185, 651, 8463, 8463, 279,
    30175609, 1114345095, 8914758577, 241407055, 10344798171, 1995,
    651, 18835677221, 6573, 10344798171, 13167, 5901,
    1995, 651, 28544495, 1054110225, 8432879735, 228358025,
    6207421725, 12825, 4185, 11306983395, 42255, 6207421725,
    84645, 37935, 12825, 4185
  ]
def negativeCoefficients : Array ℕ := #[
    10866184947426178950026628169728, 729888221459065691810669002752, 3919186391463175955750584320, 159861550178103229774036992, 2657464242116265864883637059584, 3228171948757826510920876032,
    729888221459065691810669002752, 3233328772957120163494232064, 2898135200003032746226089984, 3919186391463175955750584320, 159861550178103229774036992, 5615359023111667678650921123840,
    5615349070163985179634705629184, 310877380689353252137458466816, 136222056006325347777773568000, 136221466702027483034010255360, 109267551280048643326643011584, 4391800829068770048737280,
    73782253928355336818786304, 159861550178103229774036992, 5270160994882524058484736, 84322575918120384935755776, 6148521160696278068232192, 159861550178103229774036992,
    159861550178103229774036992, 84322575918120384935755776, 1972796932417691505892786176, 158104829846475721754542080, 73782253928355336818786304, 159861550178103229774036992,
    6148521160696278068232192, 158104829846475721754542080, 6148521160696278068232192, 159861550178103229774036992, 159861550178103229774036992, 5270160994882524058484736,
    2226566945965306436518936576, 82224155109034229191755694080, 82224134974413072737780105216, 2226587080586462890494525440, 23853480544326957342803361792, 150737938133199075221176320,
    6148521160696278068232192, 86864229287696936585903734784, 124160459567608711958495232, 23853480544326957342803361792, 124358798959889237057470464, 111466738461655105624080384,
    150737938133199075221176320, 6148521160696278068232192, 2106211975913127710220615680, 77779606184221568154363494400, 77779587137958312049251450880, 2106231022176383815332659200,
    458026879674638688164669030400, 3876118409139404791401676800, 158104829846475721754542080, 1668616231465988449400059330560, 3192697531738509736075591680, 458026879674638688164669030400,
    3197797687540008952906383360, 2866287560442559858904924160, 3876118409139404791401676800, 158104829846475721754542080
  ]
def negativeScales : Array ℕ := #[
    43, 38, 14, 13, 39, 16,
    38, 17, 16, 14, 13, 42,
    42, 24, 35, 35, 12, 8,
    10, 13, 8, 8, 9, 13,
    13, 8, 16, 12, 10, 13,
    9, 12, 9, 13, 13, 8,
    24, 30, 33, 27, 33, 10,
    9, 34, 12, 33, 13, 12,
    10, 9, 24, 29, 32, 27,
    32, 13, 12, 33, 15, 32,
    16, 15, 13, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    43099616449166997, 38203590291487405, 14662612749280074, 13046953451306728, 39067893126121895, 16382775987852475,
    38203590291487405, 17385078773721895, 16227183461140779, 14662612749280074, 13046953451306728, 42147221112221683,
    42147218555113415, 24972260417439156, 35781875064300134, 35781868823106454, 12463779785335462, 8861086908132560,
    10931476241484805, 13046953451306728, 8124121311829188, 8124121311829188, 9346513733165637, 13046953451306728,
    13046953451306728, 8124121311829188, 16672301023545835, 12031011907437707, 10931476241484805, 13046953451306728,
    9346513733165637, 12031011907437707, 9346513733165637, 13046953451306728, 13046953451306728, 8124121311829188,
    24846879553390760, 30053548935628698, 33053548582349037, 27846892599478467, 33268186447088670, 10962173043893966,
    9346513733165637, 34132748853983408, 12682336269758884, 33268186447088670, 13684639055631019, 12526743743000334,
    10962173043893966, 9346513733165637, 24766709203397615, 29973378602332297, 32973378249052547, 27766722249485004,
    32531347018256009, 13646671205401350, 12031011907437707, 33396495031024919, 15366834443983451, 32531347018256009,
    16369137229852872, 15211241917271758, 13646671205401350, 12031011907437707
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
noncomputable def negativeCeiling : ℝ := 2939732769 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 10866184947426178950026628169728, coefficient := (-10866184947426178950026628169728) }, { argument := 729888221459065691810669002752, coefficient := (-729888221459065691810669002752) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 2657464242116265864883637059584, coefficient := (-2657464242116265864883637059584) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 729888221459065691810669002752, coefficient := (-729888221459065691810669002752) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 5615359023111667678650921123840, coefficient := (-5615359023111667678650921123840) }, { argument := 5615349070163985179634705629184, coefficient := (-5615349070163985179634705629184) }, { argument := 310877380689353252137458466816, coefficient := (-310877380689353252137458466816) }, { argument := 136222056006325347777773568000, coefficient := (-136222056006325347777773568000) }, { argument := 136221466702027483034010255360, coefficient := (-136221466702027483034010255360) }, { argument := 109267551280048643326643011584, coefficient := (-109267551280048643326643011584) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 5270160994882524058484736, coefficient := (-5270160994882524058484736) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 1972796932417691505892786176, coefficient := (-1972796932417691505892786176) }, { argument := 158104829846475721754542080, coefficient := (-158104829846475721754542080) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 158104829846475721754542080, coefficient := (-158104829846475721754542080) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 5270160994882524058484736, coefficient := (-5270160994882524058484736) }, { argument := 2226566945965306436518936576, coefficient := (-2226566945965306436518936576) }, { argument := 82224155109034229191755694080, coefficient := (-82224155109034229191755694080) }, { argument := 82224134974413072737780105216, coefficient := (-82224134974413072737780105216) }, { argument := 2226587080586462890494525440, coefficient := (-2226587080586462890494525440) }, { argument := 23853480544326957342803361792, coefficient := (-23853480544326957342803361792) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 86864229287696936585903734784, coefficient := (-86864229287696936585903734784) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 23853480544326957342803361792, coefficient := (-23853480544326957342803361792) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 2106211975913127710220615680, coefficient := (-2106211975913127710220615680) }, { argument := 77779606184221568154363494400, coefficient := (-77779606184221568154363494400) }, { argument := 77779587137958312049251450880, coefficient := (-77779587137958312049251450880) }, { argument := 2106231022176383815332659200, coefficient := (-2106231022176383815332659200) }, { argument := 458026879674638688164669030400, coefficient := (-458026879674638688164669030400) }, { argument := 3876118409139404791401676800, coefficient := (-3876118409139404791401676800) }, { argument := 158104829846475721754542080, coefficient := (-158104829846475721754542080) }, { argument := 1668616231465988449400059330560, coefficient := (-1668616231465988449400059330560) }, { argument := 3192697531738509736075591680, coefficient := (-3192697531738509736075591680) }, { argument := 458026879674638688164669030400, coefficient := (-458026879674638688164669030400) }, { argument := 3197797687540008952906383360, coefficient := (-3197797687540008952906383360) }, { argument := 2866287560442559858904924160, coefficient := (-2866287560442559858904924160) }, { argument := 3876118409139404791401676800, coefficient := (-3876118409139404791401676800) }, { argument := 158104829846475721754542080, coefficient := (-158104829846475721754542080) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
