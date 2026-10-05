import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 16, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

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
def constantNumerator : ℤ := (-382492894851254737731118851686400)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    38342025, 3275505009, 54036155727, 85003650741, 56526073029, 26899889475,
    3227986737, 85003650741, 168931305903, 26899889475, 2607137287917, 166779314745,
    54036159579, 85003650741, 3227986737, 166779314745, 3227986737, 85003650741,
    85003650741, 3275505009, 18404559, 3227986737, 806996781, 4601043,
    1567443, 741046797, 28129545543, 2964189221, 1567443, 226894297,
    43717029, 3693485743, 457429401, 20259111, 7386968789, 20259111,
    39451953, 745322031, 39451953, 457429401, 745322031, 56723799,
    39451953, 39451953, 43717029, 39451953, 1783156503, 4957815,
    745322031, 33687199881, 93662505, 484653387, 85003650741, 21250915233,
    121160799, 39451953, 1783156503, 4957815, 963171921, 168931305903,
    42232831539, 240787917, 4042353, 1911120687
  ]
def negativeCoefficients : Array ℕ := #[
    707285522442773470799462400, 7552800326647087691169005568, 124598891927885462211190063104, 196005073818777285730272018432, 130340250332222384197607620608, 124053844189099547930551910400,
    7443230651345972875833114624, 196005073818777285730272018432, 194764535376886290250966499328, 124053844189099547930551910400, 3005824644701882046357272788992, 192283458493104299292355461120,
    124598900809992733702339166208, 196005073818777285730272018432, 7443230651345972875833114624, 192283458493104299292355461120, 7443230651345972875833114624, 196005073818777285730272018432,
    196005073818777285730272018432, 7552800326647087691169005568, 42438023707810973947527168, 7443230651345972875833114624, 7443231543707217441532674048, 42437131346566408247967744,
    115656879484510082854551552, 13669900610901195133342973952, 129724631885369545284095311872, 13669909986458870596222582784, 115656879484510082854551552, 261591314283952806006095872,
    50402302851621162848354304, 8516598280126996252077326336, 527380193252328752730341376, 46714329472234248493596672, 8516595170697698327411032064, 46714329472234248493596672,
    45485005012438610375344128, 1718595594794302089317056512, 45485005012438610375344128, 527380193252328752730341376, 1718595594794302089317056512, 261592350760385447561527296,
    45485005012438610375344128, 45485005012438610375344128, 50402302851621162848354304, 45485005012438610375344128, 2055839478388243643580284928, 45727772234899160322539520,
    1718595594794302089317056512, 77677394345588232803384819712, 1727768259037541246781358080, 1117534624305688980618215424, 196005073818777285730272018432, 196005097317623392627027083264,
    1117511125459582083863150592, 45485005012438610375344128, 2055839478388243643580284928, 45727772234899160322539520, 1110461620354387151626960896, 194764535376886290250966499328,
    194764558727005523053438304256, 1110438270235154349155155968, 149136502493184054207184896, 17626977103530488461415940096
  ]
def negativeScales : Array ℕ := #[
    25, 31, 35, 36, 35, 34,
    31, 36, 37, 34, 41, 37,
    35, 36, 31, 37, 31, 36,
    36, 31, 24, 31, 29, 22,
    20, 29, 34, 31, 20, 27,
    25, 31, 28, 24, 32, 24,
    25, 29, 25, 28, 29, 25,
    25, 25, 25, 25, 30, 22,
    29, 34, 26, 28, 36, 34,
    26, 25, 30, 22, 29, 37,
    35, 27, 21, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25192423197887119, 31609070208830528, 35653205990124531, 36306805752392587, 35718197422761799, 34646881194009885,
    31587987504940681, 36306805752392587, 37297645753107111, 34646881194009885, 41245603693666830, 37279149409489721,
    35653206092967915, 36306805752392587, 31587987504940681, 37279149409489721, 31587987504940681, 36306805752392587,
    36306805752392587, 31609070208830528, 24133559845276328, 31587987504940681, 29587987677903891, 22133529508833551,
    20579981549762985, 29464989410493841, 34711367193829758, 31464990399971841, 20579981549762985, 27757445106614088,
    25381692023304400, 31782335863237440, 28768973856524418, 24272067532129899, 32782335336506116, 24272067532129899,
    25233593384315263, 29473288664061858, 25233593384315263, 28768973856524418, 29473288664061858, 25757450822845377,
    25233593384315263, 25233593384315263, 25381692023304400, 25233593384315263, 30731786184240952, 22241273007839948,
    29473288664061858, 34971481478751929, 26480968287586576, 28852378094544711, 36306805752392587, 34306805925355797,
    26852347758100888, 25233593384315263, 30731786184240952, 22241273007839948, 29843218094967739, 37297645753107111,
    35297645926070321, 27843187758524074, 21946763890300079, 30831771742383466
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
noncomputable def negativeCeiling : ℝ := 2920135183 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 707285522442773470799462400, coefficient := (-707285522442773470799462400) }, { argument := 7552800326647087691169005568, coefficient := (-7552800326647087691169005568) }, { argument := 124598891927885462211190063104, coefficient := (-124598891927885462211190063104) }, { argument := 196005073818777285730272018432, coefficient := (-196005073818777285730272018432) }, { argument := 130340250332222384197607620608, coefficient := (-130340250332222384197607620608) }, { argument := 124053844189099547930551910400, coefficient := (-124053844189099547930551910400) }, { argument := 7443230651345972875833114624, coefficient := (-7443230651345972875833114624) }, { argument := 196005073818777285730272018432, coefficient := (-196005073818777285730272018432) }, { argument := 194764535376886290250966499328, coefficient := (-194764535376886290250966499328) }, { argument := 124053844189099547930551910400, coefficient := (-124053844189099547930551910400) }, { argument := 3005824644701882046357272788992, coefficient := (-3005824644701882046357272788992) }, { argument := 192283458493104299292355461120, coefficient := (-192283458493104299292355461120) }, { argument := 124598900809992733702339166208, coefficient := (-124598900809992733702339166208) }, { argument := 196005073818777285730272018432, coefficient := (-196005073818777285730272018432) }, { argument := 7443230651345972875833114624, coefficient := (-7443230651345972875833114624) }, { argument := 192283458493104299292355461120, coefficient := (-192283458493104299292355461120) }, { argument := 7443230651345972875833114624, coefficient := (-7443230651345972875833114624) }, { argument := 196005073818777285730272018432, coefficient := (-196005073818777285730272018432) }, { argument := 196005073818777285730272018432, coefficient := (-196005073818777285730272018432) }, { argument := 7552800326647087691169005568, coefficient := (-7552800326647087691169005568) }, { argument := 42438023707810973947527168, coefficient := (-42438023707810973947527168) }, { argument := 7443230651345972875833114624, coefficient := (-7443230651345972875833114624) }, { argument := 7443231543707217441532674048, coefficient := (-7443231543707217441532674048) }, { argument := 42437131346566408247967744, coefficient := (-42437131346566408247967744) }, { argument := 115656879484510082854551552, coefficient := (-115656879484510082854551552) }, { argument := 13669900610901195133342973952, coefficient := (-13669900610901195133342973952) }, { argument := 129724631885369545284095311872, coefficient := (-129724631885369545284095311872) }, { argument := 13669909986458870596222582784, coefficient := (-13669909986458870596222582784) }, { argument := 115656879484510082854551552, coefficient := (-115656879484510082854551552) }, { argument := 261591314283952806006095872, coefficient := (-261591314283952806006095872) }, { argument := 50402302851621162848354304, coefficient := (-50402302851621162848354304) }, { argument := 8516598280126996252077326336, coefficient := (-8516598280126996252077326336) }, { argument := 527380193252328752730341376, coefficient := (-527380193252328752730341376) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 8516595170697698327411032064, coefficient := (-8516595170697698327411032064) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 1718595594794302089317056512, coefficient := (-1718595594794302089317056512) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 527380193252328752730341376, coefficient := (-527380193252328752730341376) }, { argument := 1718595594794302089317056512, coefficient := (-1718595594794302089317056512) }, { argument := 261592350760385447561527296, coefficient := (-261592350760385447561527296) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 50402302851621162848354304, coefficient := (-50402302851621162848354304) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 1718595594794302089317056512, coefficient := (-1718595594794302089317056512) }, { argument := 77677394345588232803384819712, coefficient := (-77677394345588232803384819712) }, { argument := 1727768259037541246781358080, coefficient := (-1727768259037541246781358080) }, { argument := 1117534624305688980618215424, coefficient := (-1117534624305688980618215424) }, { argument := 196005073818777285730272018432, coefficient := (-196005073818777285730272018432) }, { argument := 196005097317623392627027083264, coefficient := (-196005097317623392627027083264) }, { argument := 1117511125459582083863150592, coefficient := (-1117511125459582083863150592) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 1110461620354387151626960896, coefficient := (-1110461620354387151626960896) }, { argument := 194764535376886290250966499328, coefficient := (-194764535376886290250966499328) }, { argument := 194764558727005523053438304256, coefficient := (-194764558727005523053438304256) }, { argument := 1110438270235154349155155968, coefficient := (-1110438270235154349155155968) }, { argument := 149136502493184054207184896, coefficient := (-149136502493184054207184896) }, { argument := 17626977103530488461415940096, coefficient := (-17626977103530488461415940096) }] }

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
def constantNumerator : ℤ := (-1049376457181618316381026739290112)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    72544617453, 7644487991, 4042353, 457429401, 20674976751, 57483855,
    153371325, 26899889475, 6724973175, 38342025, 745322031, 33687199881,
    93662505, 14864748819, 2607137287917, 651784400121, 3716109063, 3382377,
    1599100983, 60700598277, 6396408319, 3382377, 950902215, 166779314745,
    41694833685, 237720555, 94624059, 44735825061, 1698136249359, 178943422973,
    94624059, 4566773173, 89064371119, 178128676901, 570849369, 58348881,
    295266915, 1328584311, 124633305, 12188115, 124633305, 248873445,
    14600025, 295266915, 12188115, 7904517969, 54141138243, 3019594627,
    7787375617, 6515967353, 182288159851, 53982218015, 6515967353, 5880263221,
    3019594627, 3019594627, 5880263221, 182288159851, 5880263221, 1976128041,
    7787375617, 818546361, 420938685, 21250915233
  ]
def negativeCoefficients : Array ℕ := #[
    167276499010081782076859744256, 17626989193065385768813330432, 149136502493184054207184896, 527380193252328752730341376, 23836625303474500624214654976, 530194980777614588604579840,
    707300395130182899125452800, 124053844189099547930551910400, 124053859061786957358877900800, 707285522442773470799462400, 1718595594794302089317056512, 77677394345588232803384819712,
    1727768259037541246781358080, 17137888574004331645809721344, 3005824644701882046357272788992, 3005825005067097976805611536384, 17137528208788401197470973952, 1996602972153647746120679424,
    235985652651346947565078708224, 2239456803073747939641224331264, 235985814503079450292684587008, 1996602972153647746120679424, 1096315612451783493644451840, 192283458493104299292355461120,
    192283481545769783906260746240, 1096292559786298879739166720, 3491011599177185921951858688, 412615157913254495209062924288, 3915635599276812327390982176768, 412615440907061172996507959296,
    3491011599177185921951858688, 5265130997813344682112974848, 205368457514760174517813772288, 205368382186327828020252901376, 5265156107290793514633265152, 269086718698583463951335424,
    5446713214438751911689584640, 6127013691340684461965574144, 4598157360791170055940341760, 224831038145940491694243840, 4598157360791170055940341760, 4590904746657430040079237120,
    269322924644761296332390400, 5446713214438751911689584640, 224831038145940491694243840, 18226577500022676404450623488, 124840965128493726983925006336, 13925422322654363504563191808,
    17956465626580626624305168384, 240396764306875327868248784896, 420327879054856708940367921152, 124474520031737280640350945280, 240396764306875327868248784896, 13558963840479248675495739392,
    13925422322654363504563191808, 13925422322654363504563191808, 13558963840479248675495739392, 420327879054856708940367921152, 13558963840479248675495739392, 18226564114604007918957232128,
    17956465626580626624305168384, 7549757616916634623109234688, 124239171086701467666858639360, 196005097317623392627027083264
  ]
def negativeScales : Array ℕ := #[
    36, 32, 21, 28, 34, 25,
    27, 34, 32, 25, 29, 34,
    26, 33, 41, 39, 31, 21,
    30, 35, 32, 21, 29, 37,
    35, 27, 26, 35, 40, 37,
    26, 32, 36, 37, 29, 25,
    28, 30, 26, 23, 26, 27,
    23, 28, 23, 32, 35, 31,
    32, 32, 37, 35, 32, 32,
    31, 31, 32, 37, 32, 30,
    32, 29, 28, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36078149524407017, 32831772731861490, 21946763890300079, 28768973856524418, 34267166655961305, 25776653480108848,
    27192453534329897, 34646881194009885, 32646881366973095, 25192423197887119, 29473288664061858, 34971481478751929,
    26480968287586576, 33791176034545603, 41245603693666830, 39245603866630040, 31791145698102488, 21689606040990841,
    30574613901671015, 35820991685895095, 32574614891149016, 21689606040990841, 29824721750890029, 37279149409489721,
    35279149582452931, 27824691414446617, 26495703712332241, 35380711573066003, 40627089356319397, 37380712562544003,
    26495703712332241, 32088527988279976, 36374129367267441, 37374128838091846, 29088534868494776, 25798201653393632,
    28137444468975722, 30307242637104161, 26893114405459241, 23538971681849274, 26893114405459241, 27890837064592317,
    23799467504321990, 28137444468975722, 23538971681849274, 32880030344285521, 35656006167450003, 31491707738347745,
    32858490071054229, 32601332229527905, 37407429900919789, 35651765204201992, 32601332229527905, 32453233590532957,
    31491707738347745, 31491707738347745, 32453233590532957, 37407429900919789, 32453233590532957, 30880029284784070,
    32858490071054229, 29608488889783034, 28649034861084306, 34306805925355797
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
noncomputable def negativeCeiling : ℝ := 7801141201 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 167276499010081782076859744256, coefficient := (-167276499010081782076859744256) }, { argument := 17626989193065385768813330432, coefficient := (-17626989193065385768813330432) }, { argument := 149136502493184054207184896, coefficient := (-149136502493184054207184896) }, { argument := 527380193252328752730341376, coefficient := (-527380193252328752730341376) }, { argument := 23836625303474500624214654976, coefficient := (-23836625303474500624214654976) }, { argument := 530194980777614588604579840, coefficient := (-530194980777614588604579840) }, { argument := 707300395130182899125452800, coefficient := (-707300395130182899125452800) }, { argument := 124053844189099547930551910400, coefficient := (-124053844189099547930551910400) }, { argument := 124053859061786957358877900800, coefficient := (-124053859061786957358877900800) }, { argument := 707285522442773470799462400, coefficient := (-707285522442773470799462400) }, { argument := 1718595594794302089317056512, coefficient := (-1718595594794302089317056512) }, { argument := 77677394345588232803384819712, coefficient := (-77677394345588232803384819712) }, { argument := 1727768259037541246781358080, coefficient := (-1727768259037541246781358080) }, { argument := 17137888574004331645809721344, coefficient := (-17137888574004331645809721344) }, { argument := 3005824644701882046357272788992, coefficient := (-3005824644701882046357272788992) }, { argument := 3005825005067097976805611536384, coefficient := (-3005825005067097976805611536384) }, { argument := 17137528208788401197470973952, coefficient := (-17137528208788401197470973952) }, { argument := 1996602972153647746120679424, coefficient := (-1996602972153647746120679424) }, { argument := 235985652651346947565078708224, coefficient := (-235985652651346947565078708224) }, { argument := 2239456803073747939641224331264, coefficient := (-2239456803073747939641224331264) }, { argument := 235985814503079450292684587008, coefficient := (-235985814503079450292684587008) }, { argument := 1996602972153647746120679424, coefficient := (-1996602972153647746120679424) }, { argument := 1096315612451783493644451840, coefficient := (-1096315612451783493644451840) }, { argument := 192283458493104299292355461120, coefficient := (-192283458493104299292355461120) }, { argument := 192283481545769783906260746240, coefficient := (-192283481545769783906260746240) }, { argument := 1096292559786298879739166720, coefficient := (-1096292559786298879739166720) }, { argument := 3491011599177185921951858688, coefficient := (-3491011599177185921951858688) }, { argument := 412615157913254495209062924288, coefficient := (-412615157913254495209062924288) }, { argument := 3915635599276812327390982176768, coefficient := (-3915635599276812327390982176768) }, { argument := 412615440907061172996507959296, coefficient := (-412615440907061172996507959296) }, { argument := 3491011599177185921951858688, coefficient := (-3491011599177185921951858688) }, { argument := 5265130997813344682112974848, coefficient := (-5265130997813344682112974848) }, { argument := 205368457514760174517813772288, coefficient := (-205368457514760174517813772288) }, { argument := 205368382186327828020252901376, coefficient := (-205368382186327828020252901376) }, { argument := 5265156107290793514633265152, coefficient := (-5265156107290793514633265152) }, { argument := 269086718698583463951335424, coefficient := (-269086718698583463951335424) }, { argument := 5446713214438751911689584640, coefficient := (-5446713214438751911689584640) }, { argument := 6127013691340684461965574144, coefficient := (-6127013691340684461965574144) }, { argument := 4598157360791170055940341760, coefficient := (-4598157360791170055940341760) }, { argument := 224831038145940491694243840, coefficient := (-224831038145940491694243840) }, { argument := 4598157360791170055940341760, coefficient := (-4598157360791170055940341760) }, { argument := 4590904746657430040079237120, coefficient := (-4590904746657430040079237120) }, { argument := 269322924644761296332390400, coefficient := (-269322924644761296332390400) }, { argument := 5446713214438751911689584640, coefficient := (-5446713214438751911689584640) }, { argument := 224831038145940491694243840, coefficient := (-224831038145940491694243840) }, { argument := 18226577500022676404450623488, coefficient := (-18226577500022676404450623488) }, { argument := 124840965128493726983925006336, coefficient := (-124840965128493726983925006336) }, { argument := 13925422322654363504563191808, coefficient := (-13925422322654363504563191808) }, { argument := 17956465626580626624305168384, coefficient := (-17956465626580626624305168384) }, { argument := 240396764306875327868248784896, coefficient := (-240396764306875327868248784896) }, { argument := 420327879054856708940367921152, coefficient := (-420327879054856708940367921152) }, { argument := 124474520031737280640350945280, coefficient := (-124474520031737280640350945280) }, { argument := 240396764306875327868248784896, coefficient := (-240396764306875327868248784896) }, { argument := 13558963840479248675495739392, coefficient := (-13558963840479248675495739392) }, { argument := 13925422322654363504563191808, coefficient := (-13925422322654363504563191808) }, { argument := 13925422322654363504563191808, coefficient := (-13925422322654363504563191808) }, { argument := 13558963840479248675495739392, coefficient := (-13558963840479248675495739392) }, { argument := 420327879054856708940367921152, coefficient := (-420327879054856708940367921152) }, { argument := 13558963840479248675495739392, coefficient := (-13558963840479248675495739392) }, { argument := 18226564114604007918957232128, coefficient := (-18226564114604007918957232128) }, { argument := 17956465626580626624305168384, coefficient := (-17956465626580626624305168384) }, { argument := 7549757616916634623109234688, coefficient := (-7549757616916634623109234688) }, { argument := 124239171086701467666858639360, coefficient := (-124239171086701467666858639360) }, { argument := 196005097317623392627027083264, coefficient := (-196005097317623392627027083264) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
