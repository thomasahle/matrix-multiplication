import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-92781889123184768895840183583244288)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    101820632433, 426460428233507, 42089811308820555, 1148350873767, 1684452262056985369, 1177662713251,
    37536043067, 1148350873767, 653598362217, 1177662713251, 18390889645101, 22532779965,
    42089829680311963, 1148350873767, 37536043067, 22532779965, 37536043067, 577923561971,
    653598362217, 1705901844796611, 6493159857659597, 2807047035, 116823481855930571, 69459483015,
    2209802985, 29205425480631175, 1134763695, 1134763695, 38402792415, 2090354175,
    69459483015, 38402792415, 6496731503158117, 2209802985, 2090354175, 2807047035,
    4695, 19719, 85449, 2817, 2817, 6573,
    85449, 85449, 2817, 1054497, 42255, 19719,
    85449, 6573, 42255, 6573, 85449, 85449,
    2817, 948492791, 35026576905, 280212546623, 7588010945, 6133038299244591,
    5985, 1953, 42061494860026217, 19719
  ]
def negativeCoefficients : Array ℕ := #[
    117391196744675082118373572608, 480151756420171069230172602368, 47388914631624685009651441336320, 2647916834400074081400923357184, 474131161232701774115995138392064, 2715505334561449411576648957952,
    86552222499586093988429430784, 2647916834400074081400923357184, 1507095214351589207995878211584, 2715505334561449411576648957952, 42406504321376653837966510129152, 1662625701134260271528552693760,
    47388935316085149836918665510912, 2647916834400074081400923357184, 86552222499586093988429430784, 1662625701134260271528552693760, 86552222499586093988429430784, 2665202010461414761300999798784,
    1507095214351589207995878211584, 480168682034791187522116386816, 14621296157706411948396884525056, 103561756515020436629744517120, 526126189354492820027191869833216, 2562602613339761017029635604480,
    81527340235228854368096747520, 526118173247069395093774611251200, 83730781863208012594261524480, 83730781863208012594261524480, 1416812966790598739423951585280, 77120456979270537915767193600,
    2562602613339761017029635604480, 1416812966790598739423951585280, 14629338788374529039108214358016, 81527340235228854368096747520, 77120456979270537915767193600, 103561756515020436629744517120,
    88686042548291937113210880, 1489925514811304543501942784, 3228171948757826510920876032, 106423251057950324535853056, 1702772016927205192573648896, 124160459567608711958495232,
    3228171948757826510920876032, 3228171948757826510920876032, 1702772016927205192573648896, 39837770312692738151254327296, 3192697531738509736075591680, 1489925514811304543501942784,
    3228171948757826510920876032, 124160459567608711958495232, 3192697531738509736075591680, 124160459567608711958495232, 3228171948757826510920876032, 3228171948757826510920876032,
    106423251057950324535853056, 69986415085341929342473601024, 2584505199778562393243564113920, 2584504566898443340379412496384, 69987047965460982206625218560, 13810374499563460283542240493568,
    1808855257598388902654115840, 73782253928355336818786304, 47357033144565025922770333073408, 1489925514811304543501942784
  ]
def negativeScales : Array ℕ := #[
    36, 48, 55, 40, 60, 40,
    35, 40, 39, 40, 44, 34,
    55, 40, 35, 34, 35, 39,
    39, 50, 52, 31, 56, 36,
    31, 54, 30, 30, 35, 30,
    36, 35, 52, 31, 30, 31,
    12, 14, 16, 11, 11, 12,
    16, 16, 11, 20, 15, 14,
    16, 12, 15, 12, 16, 16,
    11, 29, 35, 38, 32, 52,
    12, 10, 55, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36567238975439269, 48599405206807088, 55224320560201807, 40062700657405439, 60546985250550617, 40099063544034260,
    35127557522630594, 40062700657405439, 39249613412152214, 40099063544034260, 44064056504233415, 34391306264857276,
    55224321189913676, 40062700657405439, 35127557522630594, 34391306264857276, 35127557522630594, 39072087733618719,
    39249613412152214, 50599456061707817, 52527842151390779, 31386406091898953, 56697107902372169, 36015452621694530,
    31041270605850262, 54697085921169215, 30079744753664897, 30079744753664897, 35160492167549259, 30961100269724102,
    36015452621694530, 35160492167549259, 52528635506044080, 31041270605850262, 30961100269724102, 31386406091898953,
    12196909442541137, 14267298770432535, 16382775987852475, 11459943848374998, 11459943848374998, 12682336269758884,
    16382775987852475, 16382775987852475, 11459943848374998, 20008123560054376, 15366834443983451, 14267298770432535,
    16382775987852475, 12682336269758884, 15366834443983451, 12682336269758884, 16382775987852475, 16382775987852475,
    11459943848374998, 29821061568589827, 35027730951472967, 38027730598193306, 32821074614677381, 52445523383576168,
    12547135531832084, 10931476241484805, 55223349642371700, 14267298770432535
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
noncomputable def negativeCeiling : ℝ := 1212455007011 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 117391196744675082118373572608, coefficient := (-117391196744675082118373572608) }, { argument := 480151756420171069230172602368, coefficient := (-480151756420171069230172602368) }, { argument := 47388914631624685009651441336320, coefficient := (-47388914631624685009651441336320) }, { argument := 2647916834400074081400923357184, coefficient := (-2647916834400074081400923357184) }, { argument := 474131161232701774115995138392064, coefficient := (-474131161232701774115995138392064) }, { argument := 2715505334561449411576648957952, coefficient := (-2715505334561449411576648957952) }, { argument := 86552222499586093988429430784, coefficient := (-86552222499586093988429430784) }, { argument := 2647916834400074081400923357184, coefficient := (-2647916834400074081400923357184) }, { argument := 1507095214351589207995878211584, coefficient := (-1507095214351589207995878211584) }, { argument := 2715505334561449411576648957952, coefficient := (-2715505334561449411576648957952) }, { argument := 42406504321376653837966510129152, coefficient := (-42406504321376653837966510129152) }, { argument := 1662625701134260271528552693760, coefficient := (-1662625701134260271528552693760) }, { argument := 47388935316085149836918665510912, coefficient := (-47388935316085149836918665510912) }, { argument := 2647916834400074081400923357184, coefficient := (-2647916834400074081400923357184) }, { argument := 86552222499586093988429430784, coefficient := (-86552222499586093988429430784) }, { argument := 1662625701134260271528552693760, coefficient := (-1662625701134260271528552693760) }, { argument := 86552222499586093988429430784, coefficient := (-86552222499586093988429430784) }, { argument := 2665202010461414761300999798784, coefficient := (-2665202010461414761300999798784) }, { argument := 1507095214351589207995878211584, coefficient := (-1507095214351589207995878211584) }, { argument := 480168682034791187522116386816, coefficient := (-480168682034791187522116386816) }, { argument := 14621296157706411948396884525056, coefficient := (-14621296157706411948396884525056) }, { argument := 103561756515020436629744517120, coefficient := (-103561756515020436629744517120) }, { argument := 526126189354492820027191869833216, coefficient := (-526126189354492820027191869833216) }, { argument := 2562602613339761017029635604480, coefficient := (-2562602613339761017029635604480) }, { argument := 81527340235228854368096747520, coefficient := (-81527340235228854368096747520) }, { argument := 526118173247069395093774611251200, coefficient := (-526118173247069395093774611251200) }, { argument := 83730781863208012594261524480, coefficient := (-83730781863208012594261524480) }, { argument := 83730781863208012594261524480, coefficient := (-83730781863208012594261524480) }, { argument := 1416812966790598739423951585280, coefficient := (-1416812966790598739423951585280) }, { argument := 77120456979270537915767193600, coefficient := (-77120456979270537915767193600) }, { argument := 2562602613339761017029635604480, coefficient := (-2562602613339761017029635604480) }, { argument := 1416812966790598739423951585280, coefficient := (-1416812966790598739423951585280) }, { argument := 14629338788374529039108214358016, coefficient := (-14629338788374529039108214358016) }, { argument := 81527340235228854368096747520, coefficient := (-81527340235228854368096747520) }, { argument := 77120456979270537915767193600, coefficient := (-77120456979270537915767193600) }, { argument := 103561756515020436629744517120, coefficient := (-103561756515020436629744517120) }, { argument := 88686042548291937113210880, coefficient := (-88686042548291937113210880) }, { argument := 1489925514811304543501942784, coefficient := (-1489925514811304543501942784) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 106423251057950324535853056, coefficient := (-106423251057950324535853056) }, { argument := 1702772016927205192573648896, coefficient := (-1702772016927205192573648896) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 1702772016927205192573648896, coefficient := (-1702772016927205192573648896) }, { argument := 39837770312692738151254327296, coefficient := (-39837770312692738151254327296) }, { argument := 3192697531738509736075591680, coefficient := (-3192697531738509736075591680) }, { argument := 1489925514811304543501942784, coefficient := (-1489925514811304543501942784) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 3192697531738509736075591680, coefficient := (-3192697531738509736075591680) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 106423251057950324535853056, coefficient := (-106423251057950324535853056) }, { argument := 69986415085341929342473601024, coefficient := (-69986415085341929342473601024) }, { argument := 2584505199778562393243564113920, coefficient := (-2584505199778562393243564113920) }, { argument := 2584504566898443340379412496384, coefficient := (-2584504566898443340379412496384) }, { argument := 69987047965460982206625218560, coefficient := (-69987047965460982206625218560) }, { argument := 13810374499563460283542240493568, coefficient := (-13810374499563460283542240493568) }, { argument := 1808855257598388902654115840, coefficient := (-1808855257598388902654115840) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 47357033144565025922770333073408, coefficient := (-47357033144565025922770333073408) }, { argument := 1489925514811304543501942784, coefficient := (-1489925514811304543501942784) }] }

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


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-101314602782648611941194031249227776)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    12266076464520761, 39501, 17703, 5985, 1953, 30175609,
    1114345095, 8914758577, 241407055, 316538558151, 25935, 8463,
    576245700921, 85449, 316538558151, 171171, 76713, 25935,
    8463, 229311843705, 229311275655, 123067972893987, 12274497037340121, 630800359257,
    492935206909630495, 647222727261, 20615192517, 630800359257, 358750213527, 647222727261,
    10104664267731, 12370201155, 12274502389052081, 630800359257, 20615192517, 12370201155,
    20615192517, 317461165581, 358750213527, 492273844961581, 12986116138525327, 22456370781,
    233643405113332491, 555675728049, 17678419551, 934559380971901249, 9078107337, 9078107337,
    307222264089, 16722829305, 555675728049, 307222264089, 25986518869663093, 17678419551,
    16722829305, 22456370781, 30778282084027391, 855, 279, 1682799280683647215,
    2817, 492452507997224737, 5643, 2529
  ]
def negativeCoefficients : Array ℕ := #[
    13810374348728427559788807716864, 1492305587518670844689645568, 1337600861539861267488964608, 1808855257598388902654115840, 73782253928355336818786304, 2226566945965306436518936576,
    82224155109034229191755694080, 82224134974413072737780105216, 2226587080586462890494525440, 729888221459065691810669002752, 3919186391463175955750584320, 159861550178103229774036992,
    2657464242116265864883637059584, 3228171948757826510920876032, 729888221459065691810669002752, 3233328772957120163494232064, 2898135200003032746226089984, 3919186391463175955750584320,
    159861550178103229774036992, 264378555868538731233363886080, 264377900951478039313939169280, 138562219216650538857044901888, 13819855070881306515520308117504, 727263299301120053002824056832,
    138748925884750640150563489054720, 746197000529499075380810612736, 23767698774459452806599278592, 727263299301120053002824056832, 413610835957576466826214244352, 746197000529499075380810612736,
    11649884731099468141791811731456, 456379869693182601069550632960, 13819861096373303728077006700544, 727263299301120053002824056832, 23767698774459452806599278592, 456379869693182601069550632960,
    23767698774459452806599278592, 732015609351779804308530266112, 413610835957576466826214244352, 138562769045826094462073307136, 14621066950613161773028027138048, 103561731155359021297538433024,
    526118176102989023107725045792768, 2562601985823032803596536119296, 81527320271240080595934511104, 526110159987581984361224956018688, 83730761359651974666094903296, 83730761359651974666094903296,
    1416812619848847887113132179456, 77120438094416292455613726720, 2562601985823032803596536119296, 1416812619848847887113132179456, 14629109587258883568200126038016, 81527320271240080595934511104,
    77120438094416292455613726720, 103561731155359021297538433024, 138613059724729771164386969255936, 129203946971313493046722560, 5270160994882524058484736, 473665888339138269048109835223040,
    106423251057950324535853056, 138613058219622970436957054697472, 106593256251333631763546112, 95542918681418661963497472
  ]
def negativeScales : Array ℕ := #[
    53, 15, 14, 12, 10, 24,
    30, 33, 27, 38, 14, 13,
    39, 16, 38, 17, 16, 14,
    13, 37, 37, 46, 53, 39,
    58, 39, 34, 39, 38, 39,
    43, 33, 53, 39, 34, 33,
    34, 38, 38, 48, 53, 34,
    57, 39, 34, 59, 33, 33,
    38, 33, 39, 38, 54, 34,
    33, 34, 54, 9, 8, 60,
    11, 58, 12, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    53445523367819249, 15269601556301956, 14111706243720843, 12547135531832084, 10931476241484805, 24846879553390760,
    30053548935628698, 33053548582349037, 27846892599478467, 38203590291487405, 14662612749280074, 13046953451306728,
    39067893126121895, 16382775987852475, 38203590291487405, 17385078773721895, 16227183461140779, 14662612749280074,
    13046953451306728, 37738519914393792, 37738516340553370, 46806448694079166, 53446513427739715, 39198392525541510,
    58774175639755347, 39235471312732594, 34262988882911841, 39198392525541510, 38384188734237127, 39235471312732594,
    43200086621821791, 33526149909411774, 53446514056758289, 39198392525541510, 34262988882911841, 33526149909411774,
    34262988882911841, 38207789164306080, 38384188734237127, 48806454418830598, 53527819535165438, 34386405738619292,
    57697085929000575, 39015452268414869, 34041270252570601, 59697063947440933, 33079744400385236, 33079744400385236,
    38160491814269598, 33961099916444367, 39015452268414869, 38160491814269598, 54528612902841841, 34041270252570601,
    33961099916444367, 34386405738619292, 54772762227228193, 9739780609952834, 8124121311829188, 60545568814509903,
    11459943848374998, 58772762211562929, 12462246634244425, 11304351321663239
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
noncomputable def negativeCeiling : ℝ := 718616408669 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13810374348728427559788807716864, coefficient := (-13810374348728427559788807716864) }, { argument := 1492305587518670844689645568, coefficient := (-1492305587518670844689645568) }, { argument := 1337600861539861267488964608, coefficient := (-1337600861539861267488964608) }, { argument := 1808855257598388902654115840, coefficient := (-1808855257598388902654115840) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 2226566945965306436518936576, coefficient := (-2226566945965306436518936576) }, { argument := 82224155109034229191755694080, coefficient := (-82224155109034229191755694080) }, { argument := 82224134974413072737780105216, coefficient := (-82224134974413072737780105216) }, { argument := 2226587080586462890494525440, coefficient := (-2226587080586462890494525440) }, { argument := 729888221459065691810669002752, coefficient := (-729888221459065691810669002752) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 2657464242116265864883637059584, coefficient := (-2657464242116265864883637059584) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 729888221459065691810669002752, coefficient := (-729888221459065691810669002752) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 264378555868538731233363886080, coefficient := (-264378555868538731233363886080) }, { argument := 264377900951478039313939169280, coefficient := (-264377900951478039313939169280) }, { argument := 138562219216650538857044901888, coefficient := (-138562219216650538857044901888) }, { argument := 13819855070881306515520308117504, coefficient := (-13819855070881306515520308117504) }, { argument := 727263299301120053002824056832, coefficient := (-727263299301120053002824056832) }, { argument := 138748925884750640150563489054720, coefficient := (-138748925884750640150563489054720) }, { argument := 746197000529499075380810612736, coefficient := (-746197000529499075380810612736) }, { argument := 23767698774459452806599278592, coefficient := (-23767698774459452806599278592) }, { argument := 727263299301120053002824056832, coefficient := (-727263299301120053002824056832) }, { argument := 413610835957576466826214244352, coefficient := (-413610835957576466826214244352) }, { argument := 746197000529499075380810612736, coefficient := (-746197000529499075380810612736) }, { argument := 11649884731099468141791811731456, coefficient := (-11649884731099468141791811731456) }, { argument := 456379869693182601069550632960, coefficient := (-456379869693182601069550632960) }, { argument := 13819861096373303728077006700544, coefficient := (-13819861096373303728077006700544) }, { argument := 727263299301120053002824056832, coefficient := (-727263299301120053002824056832) }, { argument := 23767698774459452806599278592, coefficient := (-23767698774459452806599278592) }, { argument := 456379869693182601069550632960, coefficient := (-456379869693182601069550632960) }, { argument := 23767698774459452806599278592, coefficient := (-23767698774459452806599278592) }, { argument := 732015609351779804308530266112, coefficient := (-732015609351779804308530266112) }, { argument := 413610835957576466826214244352, coefficient := (-413610835957576466826214244352) }, { argument := 138562769045826094462073307136, coefficient := (-138562769045826094462073307136) }, { argument := 14621066950613161773028027138048, coefficient := (-14621066950613161773028027138048) }, { argument := 103561731155359021297538433024, coefficient := (-103561731155359021297538433024) }, { argument := 526118176102989023107725045792768, coefficient := (-526118176102989023107725045792768) }, { argument := 2562601985823032803596536119296, coefficient := (-2562601985823032803596536119296) }, { argument := 81527320271240080595934511104, coefficient := (-81527320271240080595934511104) }, { argument := 526110159987581984361224956018688, coefficient := (-526110159987581984361224956018688) }, { argument := 83730761359651974666094903296, coefficient := (-83730761359651974666094903296) }, { argument := 83730761359651974666094903296, coefficient := (-83730761359651974666094903296) }, { argument := 1416812619848847887113132179456, coefficient := (-1416812619848847887113132179456) }, { argument := 77120438094416292455613726720, coefficient := (-77120438094416292455613726720) }, { argument := 2562601985823032803596536119296, coefficient := (-2562601985823032803596536119296) }, { argument := 1416812619848847887113132179456, coefficient := (-1416812619848847887113132179456) }, { argument := 14629109587258883568200126038016, coefficient := (-14629109587258883568200126038016) }, { argument := 81527320271240080595934511104, coefficient := (-81527320271240080595934511104) }, { argument := 77120438094416292455613726720, coefficient := (-77120438094416292455613726720) }, { argument := 103561731155359021297538433024, coefficient := (-103561731155359021297538433024) }, { argument := 138613059724729771164386969255936, coefficient := (-138613059724729771164386969255936) }, { argument := 129203946971313493046722560, coefficient := (-129203946971313493046722560) }, { argument := 5270160994882524058484736, coefficient := (-5270160994882524058484736) }, { argument := 473665888339138269048109835223040, coefficient := (-473665888339138269048109835223040) }, { argument := 106423251057950324535853056, coefficient := (-106423251057950324535853056) }, { argument := 138613058219622970436957054697472, coefficient := (-138613058219622970436957054697472) }, { argument := 106593256251333631763546112, coefficient := (-106593256251333631763546112) }, { argument := 95542918681418661963497472, coefficient := (-95542918681418661963497472) }] }

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

end TermShard3


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
