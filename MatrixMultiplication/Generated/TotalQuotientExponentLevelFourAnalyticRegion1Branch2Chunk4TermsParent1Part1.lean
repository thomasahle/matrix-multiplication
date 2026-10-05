import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-16160330019290806016612567470833664)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    89368209, 84537495, 113521779, 54027758365029, 4288676733, 429636347565723,
    6908108031, 214005825, 6908108031, 4613965587, 54588761794917, 4288676733,
    25680699, 661653747007477, 17170003473199115, 112858382875, 99960281975, 4678786101475,
    1273687463875, 8585004748563051, 4678786101475, 112858382875, 112858382875, 48367878375,
    112858382875, 1273687463875, 48367878375, 330823861540245, 99960281975, 381910759036515,
    27915903923986025, 241484724855, 256432281278029075, 247798050995, 7891657675, 241484724855,
    137314843545, 247798050995, 3868490592285, 4734994605, 13957961026628575, 241484724855,
    7891657675, 4734994605, 7891657675, 121531528195, 137314843545, 381910759036515,
    44018649, 3701494823, 1850746965, 22009771, 161329275, 11913744825,
    124174969875, 11913744825, 161329275, 264164713505529, 9545960333, 4284963932361451,
    236211741857, 7514904943, 4284966015508813, 3859005241
  ]
def negativeCoefficients : Array ℕ := #[
    206069059968598326764371968, 194930191862187606398730240, 261763400500651928592580608, 15207462027525487662962049024, 79112122108523791015401750528, 241863761850226376126628888576,
    127432100881394609479898628096, 3947710684058073403962163200, 127432100881394609479898628096, 85112642348292062589424238592, 15365370454887810599120535552, 79112122108523791015401750528,
    3789802256695750467803676672, 372477946058895731257795149824, 9665852655481207052192060538880, 260233713183481224727887872000, 230492717391083370473272115200, 10788546223692321630861865779200,
    2936923334499288107643305984000, 9665856046650623797226398285824, 10788546223692321630861865779200, 260233713183481224727887872000, 260233713183481224727887872000, 223057468442983906909618176000,
    260233713183481224727887872000, 2936923334499288107643305984000, 223057468442983906909618176000, 372474554889478986223457402880, 230492717391083370473272115200, 214996644010704030244987207680,
    15715256813721753660429225164800, 2227303458555176455587590307840, 144358540801187244993692460646400, 2285533614334396755080076328960, 72787694724025374365607526400, 2227303458555176455587590307840,
    1266505888198041513961570959360, 2285533614334396755080076328960, 35680527953717238514020809441280, 1397523738701287187819664506880, 15715267019594089041515826380800, 2227303458555176455587590307840,
    72787694724025374365607526400, 1397523738701287187819664506880, 72787694724025374365607526400, 2241860997499981530460711813120, 1266505888198041513961570959360, 214996644010704030244987207680,
    203000188143362720133021696, 17070131922510458928068820992, 17070127804274844472411422720, 203004306378977175790419968, 1487999923761054261392179200, 219769801746256589118190387200,
    2290623889644718351416557568000, 219769801746256589118190387200, 1487999923761054261392179200, 297423026326983559133156868096, 22011485900079275986194006016, 9648880984539522974931482574848,
    544667193655153148339226148864, 17328191027721983223174004736, 9648885675370364605447352090624, 17796520514957712499476004864
  ]
def negativeScales : Array ℕ := #[
    26, 26, 26, 45, 31, 48,
    32, 27, 32, 32, 45, 31,
    24, 49, 53, 36, 36, 42,
    40, 52, 42, 36, 36, 35,
    36, 40, 35, 48, 36, 48,
    54, 37, 57, 37, 32, 37,
    36, 37, 41, 32, 53, 37,
    32, 32, 32, 36, 36, 48,
    25, 31, 30, 24, 27, 33,
    36, 33, 27, 47, 33, 51,
    37, 32, 51, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26413258376215019, 26333088027531025, 26758393862533560, 45618766058713422, 31997885451121588, 48610109380028041,
    32685643498365071, 27673074824848482, 32685643498365071, 32103360097788348, 45633669207193979, 31997885451121588,
    24614181135765331, 49233069759715369, 53930739856872512, 36715722626622129, 36540635919960708, 42089271413639578,
    40212148452637299, 52930740363027866, 42089271413639578, 36715722626622129, 36715722626622129, 35493330205181569,
    36715722626622129, 40212148452637299, 35493330205181569, 48233056624855645, 36540635919960708, 48440228891981289,
    54631936789913779, 37813140978704257, 57831355503037136, 37850373885805230, 32877681232967528, 37813140978704257,
    36998696654206905, 37850373885805230, 41814907904908762, 32140715635890233, 53631937726834938, 37813140978704257,
    32877681232967528, 32140715635890233, 32877681232967528, 36822539676879850, 36998696654206905, 48440228891981289,
    25391611531592078, 31785460865263992, 30785460517208166, 24391640799041963, 27265433014487019, 33471907912979752,
    36853583442391050, 33471907912979752, 27265433014487019, 47908431101179958, 33152243195456717, 51928204491345829,
    37781289725691297, 32807107710154285, 51928205192716030, 31845581858814321
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
noncomputable def negativeCeiling : ℝ := 94579209107 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 206069059968598326764371968, coefficient := (-206069059968598326764371968) }, { argument := 194930191862187606398730240, coefficient := (-194930191862187606398730240) }, { argument := 261763400500651928592580608, coefficient := (-261763400500651928592580608) }, { argument := 15207462027525487662962049024, coefficient := (-15207462027525487662962049024) }, { argument := 79112122108523791015401750528, coefficient := (-79112122108523791015401750528) }, { argument := 241863761850226376126628888576, coefficient := (-241863761850226376126628888576) }, { argument := 127432100881394609479898628096, coefficient := (-127432100881394609479898628096) }, { argument := 3947710684058073403962163200, coefficient := (-3947710684058073403962163200) }, { argument := 127432100881394609479898628096, coefficient := (-127432100881394609479898628096) }, { argument := 85112642348292062589424238592, coefficient := (-85112642348292062589424238592) }, { argument := 15365370454887810599120535552, coefficient := (-15365370454887810599120535552) }, { argument := 79112122108523791015401750528, coefficient := (-79112122108523791015401750528) }, { argument := 3789802256695750467803676672, coefficient := (-3789802256695750467803676672) }, { argument := 372477946058895731257795149824, coefficient := (-372477946058895731257795149824) }, { argument := 9665852655481207052192060538880, coefficient := (-9665852655481207052192060538880) }, { argument := 260233713183481224727887872000, coefficient := (-260233713183481224727887872000) }, { argument := 230492717391083370473272115200, coefficient := (-230492717391083370473272115200) }, { argument := 10788546223692321630861865779200, coefficient := (-10788546223692321630861865779200) }, { argument := 2936923334499288107643305984000, coefficient := (-2936923334499288107643305984000) }, { argument := 9665856046650623797226398285824, coefficient := (-9665856046650623797226398285824) }, { argument := 10788546223692321630861865779200, coefficient := (-10788546223692321630861865779200) }, { argument := 260233713183481224727887872000, coefficient := (-260233713183481224727887872000) }, { argument := 260233713183481224727887872000, coefficient := (-260233713183481224727887872000) }, { argument := 223057468442983906909618176000, coefficient := (-223057468442983906909618176000) }, { argument := 260233713183481224727887872000, coefficient := (-260233713183481224727887872000) }, { argument := 2936923334499288107643305984000, coefficient := (-2936923334499288107643305984000) }, { argument := 223057468442983906909618176000, coefficient := (-223057468442983906909618176000) }, { argument := 372474554889478986223457402880, coefficient := (-372474554889478986223457402880) }, { argument := 230492717391083370473272115200, coefficient := (-230492717391083370473272115200) }, { argument := 214996644010704030244987207680, coefficient := (-214996644010704030244987207680) }, { argument := 15715256813721753660429225164800, coefficient := (-15715256813721753660429225164800) }, { argument := 2227303458555176455587590307840, coefficient := (-2227303458555176455587590307840) }, { argument := 144358540801187244993692460646400, coefficient := (-144358540801187244993692460646400) }, { argument := 2285533614334396755080076328960, coefficient := (-2285533614334396755080076328960) }, { argument := 72787694724025374365607526400, coefficient := (-72787694724025374365607526400) }, { argument := 2227303458555176455587590307840, coefficient := (-2227303458555176455587590307840) }, { argument := 1266505888198041513961570959360, coefficient := (-1266505888198041513961570959360) }, { argument := 2285533614334396755080076328960, coefficient := (-2285533614334396755080076328960) }, { argument := 35680527953717238514020809441280, coefficient := (-35680527953717238514020809441280) }, { argument := 1397523738701287187819664506880, coefficient := (-1397523738701287187819664506880) }, { argument := 15715267019594089041515826380800, coefficient := (-15715267019594089041515826380800) }, { argument := 2227303458555176455587590307840, coefficient := (-2227303458555176455587590307840) }, { argument := 72787694724025374365607526400, coefficient := (-72787694724025374365607526400) }, { argument := 1397523738701287187819664506880, coefficient := (-1397523738701287187819664506880) }, { argument := 72787694724025374365607526400, coefficient := (-72787694724025374365607526400) }, { argument := 2241860997499981530460711813120, coefficient := (-2241860997499981530460711813120) }, { argument := 1266505888198041513961570959360, coefficient := (-1266505888198041513961570959360) }, { argument := 214996644010704030244987207680, coefficient := (-214996644010704030244987207680) }, { argument := 203000188143362720133021696, coefficient := (-203000188143362720133021696) }, { argument := 17070131922510458928068820992, coefficient := (-17070131922510458928068820992) }, { argument := 17070127804274844472411422720, coefficient := (-17070127804274844472411422720) }, { argument := 203004306378977175790419968, coefficient := (-203004306378977175790419968) }, { argument := 1487999923761054261392179200, coefficient := (-1487999923761054261392179200) }, { argument := 219769801746256589118190387200, coefficient := (-219769801746256589118190387200) }, { argument := 2290623889644718351416557568000, coefficient := (-2290623889644718351416557568000) }, { argument := 219769801746256589118190387200, coefficient := (-219769801746256589118190387200) }, { argument := 1487999923761054261392179200, coefficient := (-1487999923761054261392179200) }, { argument := 297423026326983559133156868096, coefficient := (-297423026326983559133156868096) }, { argument := 22011485900079275986194006016, coefficient := (-22011485900079275986194006016) }, { argument := 9648880984539522974931482574848, coefficient := (-9648880984539522974931482574848) }, { argument := 544667193655153148339226148864, coefficient := (-544667193655153148339226148864) }, { argument := 17328191027721983223174004736, coefficient := (-17328191027721983223174004736) }, { argument := 9648885675370364605447352090624, coefficient := (-9648885675370364605447352090624) }, { argument := 17796520514957712499476004864, coefficient := (-17796520514957712499476004864) }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3475764503609697167563064602525696)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3859005241, 130596861577, 7108693865, 236211741857, 130596861577, 264162586453143,
    7514904943, 7108693865, 9545960333, 5137875, 379418625, 3954616875,
    379418625, 5137875, 391241515, 14178722005, 113429817725, 3129890435,
    774734819505, 21139533520123, 6197877120381, 44018649, 3701494823, 1850746965,
    22009771, 1489683753, 125266377431, 62633173605, 744856987, 157218975,
    11610209925, 121011276375, 11610209925, 157218975, 81086985, 6818543095,
    3409270725, 40544315, 89399025, 6601884075, 68810333625, 6601884075,
    89399025, 346528199, 12558296633, 100466409985, 2772188671, 2694404673,
    226570446271, 113285195805, 1347229667, 161329275, 11913744825, 124174969875,
    11913744825, 161329275, 1489683753, 125266377431, 62633173605, 744856987,
    2518586325, 185991009975, 1938553192125, 185991009975
  ]
def negativeCoefficients : Array ℕ := #[
    17796520514957712499476004864, 301135860292573924662186082304, 16391532053250524670570004480, 544667193655153148339226148864, 301135860292573924662186082304, 297420631478900312352051167232,
    17328191027721983223174004736, 16391532053250524670570004480, 22011485900079275986194006016, 47388532603855231254528000, 6999038272173776723509248000, 72949805402698036669317120000,
    6999038272173776723509248000, 47388532603855231254528000, 7217132098215396644214538240, 261551256118508961476462510080, 261551352237574800549294899200, 7217035979149557571382149120,
    13956381777734665905289297920, 47601997642006026202596245504, 13956378544917997189739839488, 203000188143362720133021696, 17070131922510458928068820992, 17070127804274844472411422720,
    203004306378977175790419968, 3434976867794269185408761856, 288844600688795397124953997312, 288844531003913815677909073920, 3435046552675850632453685248, 1450089097677970076388556800,
    214170571128517567739382988800, 2232264045322559922081103872000, 214170571128517567739382988800, 1450089097677970076388556800, 186973857500465663280414720, 15722489928628054275852861440,
    15722486135516304119326310400, 186977650612215819806965760, 824560467307081023828787200, 121783265935823714989060915200, 1269326614006945838046117888000, 121783265935823714989060915200,
    824560467307081023828787200, 6392317001276494170590019584, 231659683990679365879152508928, 231659769124709109057946910720, 6392231867246750991795617792, 6212874179229759039860637696,
    522435879628412203509053652992, 522435753588727476879328542720, 6213000218914485669585747968, 1487999923761054261392179200, 219769801746256589118190387200, 2290623889644718351416557568000,
    219769801746256589118190387200, 1487999923761054261392179200, 3434976867794269185408761856, 288844600688795397124953997312, 288844531003913815677909073920, 3435046552675850632453685248,
    23229858682409834360969625600, 3430928561019585349864233369600, 35759994608402577575299252224000, 3430928561019585349864233369600
  ]
def negativeScales : Array ℕ := #[
    31, 36, 32, 37, 36, 47,
    32, 32, 33, 22, 28, 31,
    28, 22, 28, 33, 36, 31,
    39, 44, 42, 25, 31, 30,
    24, 30, 36, 35, 29, 27,
    33, 36, 33, 27, 26, 32,
    31, 25, 26, 32, 36, 32,
    26, 28, 33, 36, 31, 31,
    37, 36, 30, 27, 33, 36,
    33, 27, 30, 36, 35, 29,
    31, 37, 40, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31845581858814321, 36926329278057291, 32726937360858749, 37781289725691297, 36926329278057291, 47908419484561981,
    32807107710154285, 32726937360858749, 33152243195456717, 22292740360482754, 28499215258975648, 31880890789620445,
    28499215258975648, 22292740360482754, 28543484223221510, 33723008450534821, 36723008980719522, 31543465009021026,
    39494911625048123, 44265008775079841, 42494911290866299, 25391611531592078, 31785460865263992, 30785460517208166,
    24391640799041963, 30472358945476540, 36866208281022125, 35866207932966287, 29472388212926425, 27228200108288044,
    33434675006780699, 36816350535235970, 33434675006780699, 27228200108288044, 26272967035093454, 32666816368318971,
    31666816020263148, 25272996302543340, 26413755761444132, 32620230659946553, 36001906187493695, 32620230659946553,
    26413755761444132, 28368397516662330, 33547921743854751, 36547922274039450, 31368378302461847, 31327319399621706,
    37721168732932902, 36721168384877078, 30327348667071592, 27265433014487019, 33471907912979752, 36853583442391050,
    33471907912979752, 27265433014487019, 30472358945476540, 36866208281022125, 35866207932966287, 29472388212926425,
    31229967034462231, 37436441932954889, 40818117461442344, 37436441932954889
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
noncomputable def negativeCeiling : ℝ := 2590389177 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17796520514957712499476004864, coefficient := (-17796520514957712499476004864) }, { argument := 301135860292573924662186082304, coefficient := (-301135860292573924662186082304) }, { argument := 16391532053250524670570004480, coefficient := (-16391532053250524670570004480) }, { argument := 544667193655153148339226148864, coefficient := (-544667193655153148339226148864) }, { argument := 301135860292573924662186082304, coefficient := (-301135860292573924662186082304) }, { argument := 297420631478900312352051167232, coefficient := (-297420631478900312352051167232) }, { argument := 17328191027721983223174004736, coefficient := (-17328191027721983223174004736) }, { argument := 16391532053250524670570004480, coefficient := (-16391532053250524670570004480) }, { argument := 22011485900079275986194006016, coefficient := (-22011485900079275986194006016) }, { argument := 47388532603855231254528000, coefficient := (-47388532603855231254528000) }, { argument := 6999038272173776723509248000, coefficient := (-6999038272173776723509248000) }, { argument := 72949805402698036669317120000, coefficient := (-72949805402698036669317120000) }, { argument := 6999038272173776723509248000, coefficient := (-6999038272173776723509248000) }, { argument := 47388532603855231254528000, coefficient := (-47388532603855231254528000) }, { argument := 7217132098215396644214538240, coefficient := (-7217132098215396644214538240) }, { argument := 261551256118508961476462510080, coefficient := (-261551256118508961476462510080) }, { argument := 261551352237574800549294899200, coefficient := (-261551352237574800549294899200) }, { argument := 7217035979149557571382149120, coefficient := (-7217035979149557571382149120) }, { argument := 13956381777734665905289297920, coefficient := (-13956381777734665905289297920) }, { argument := 47601997642006026202596245504, coefficient := (-47601997642006026202596245504) }, { argument := 13956378544917997189739839488, coefficient := (-13956378544917997189739839488) }, { argument := 203000188143362720133021696, coefficient := (-203000188143362720133021696) }, { argument := 17070131922510458928068820992, coefficient := (-17070131922510458928068820992) }, { argument := 17070127804274844472411422720, coefficient := (-17070127804274844472411422720) }, { argument := 203004306378977175790419968, coefficient := (-203004306378977175790419968) }, { argument := 3434976867794269185408761856, coefficient := (-3434976867794269185408761856) }, { argument := 288844600688795397124953997312, coefficient := (-288844600688795397124953997312) }, { argument := 288844531003913815677909073920, coefficient := (-288844531003913815677909073920) }, { argument := 3435046552675850632453685248, coefficient := (-3435046552675850632453685248) }, { argument := 1450089097677970076388556800, coefficient := (-1450089097677970076388556800) }, { argument := 214170571128517567739382988800, coefficient := (-214170571128517567739382988800) }, { argument := 2232264045322559922081103872000, coefficient := (-2232264045322559922081103872000) }, { argument := 214170571128517567739382988800, coefficient := (-214170571128517567739382988800) }, { argument := 1450089097677970076388556800, coefficient := (-1450089097677970076388556800) }, { argument := 186973857500465663280414720, coefficient := (-186973857500465663280414720) }, { argument := 15722489928628054275852861440, coefficient := (-15722489928628054275852861440) }, { argument := 15722486135516304119326310400, coefficient := (-15722486135516304119326310400) }, { argument := 186977650612215819806965760, coefficient := (-186977650612215819806965760) }, { argument := 824560467307081023828787200, coefficient := (-824560467307081023828787200) }, { argument := 121783265935823714989060915200, coefficient := (-121783265935823714989060915200) }, { argument := 1269326614006945838046117888000, coefficient := (-1269326614006945838046117888000) }, { argument := 121783265935823714989060915200, coefficient := (-121783265935823714989060915200) }, { argument := 824560467307081023828787200, coefficient := (-824560467307081023828787200) }, { argument := 6392317001276494170590019584, coefficient := (-6392317001276494170590019584) }, { argument := 231659683990679365879152508928, coefficient := (-231659683990679365879152508928) }, { argument := 231659769124709109057946910720, coefficient := (-231659769124709109057946910720) }, { argument := 6392231867246750991795617792, coefficient := (-6392231867246750991795617792) }, { argument := 6212874179229759039860637696, coefficient := (-6212874179229759039860637696) }, { argument := 522435879628412203509053652992, coefficient := (-522435879628412203509053652992) }, { argument := 522435753588727476879328542720, coefficient := (-522435753588727476879328542720) }, { argument := 6213000218914485669585747968, coefficient := (-6213000218914485669585747968) }, { argument := 1487999923761054261392179200, coefficient := (-1487999923761054261392179200) }, { argument := 219769801746256589118190387200, coefficient := (-219769801746256589118190387200) }, { argument := 2290623889644718351416557568000, coefficient := (-2290623889644718351416557568000) }, { argument := 219769801746256589118190387200, coefficient := (-219769801746256589118190387200) }, { argument := 1487999923761054261392179200, coefficient := (-1487999923761054261392179200) }, { argument := 3434976867794269185408761856, coefficient := (-3434976867794269185408761856) }, { argument := 288844600688795397124953997312, coefficient := (-288844600688795397124953997312) }, { argument := 288844531003913815677909073920, coefficient := (-288844531003913815677909073920) }, { argument := 3435046552675850632453685248, coefficient := (-3435046552675850632453685248) }, { argument := 23229858682409834360969625600, coefficient := (-23229858682409834360969625600) }, { argument := 3430928561019585349864233369600, coefficient := (-3430928561019585349864233369600) }, { argument := 35759994608402577575299252224000, coefficient := (-35759994608402577575299252224000) }, { argument := 3430928561019585349864233369600, coefficient := (-3430928561019585349864233369600) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
