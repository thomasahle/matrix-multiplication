import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 15, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-950332438200870247000920794595328)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4009, 4009, 2174058579, 9345, 525, 3688080557,
    28385, 2174058579, 28385, 28385, 9345, 525,
    3999, 3999, 93, 429479819, 7515361441, 7515365127,
    429476133, 28264051767, 143913, 8085, 47955261641, 437129,
    28264051767, 437129, 437129, 143913, 8085, 4009,
    4009, 28260449847, 162603, 9135, 47926746441, 493899,
    28260449847, 493899, 493899, 162603, 9135, 63419,
    63419, 1929, 3999, 3999, 969, 379017193520031,
    5607, 315, 1337557558265235, 17031, 189508592615271, 17031,
    17031, 5607, 315, 51120391709257, 51120379927991, 5068833,
    4809, 4809, 1113, 93
  ]
def negativeCoefficients : Array ℕ := #[
    77545337773360773782352953344, 77545337773360773782352953344, 20052151104032829522504056832, 88261029564833669043978240, 4958484807013127474380800, 68033078158203172180157530112,
    134044372616254879390760960, 20052151104032829522504056832, 134044372616254879390760960, 134044372616254879390760960, 88261029564833669043978240, 4958484807013127474380800,
    77351909642222433114399965184, 77351909642222433114399965184, 3597763239173136423925579776, 3961252152958050443305418752, 138633949123552026048285638656, 138634017118250681741692895232,
    3961218155608722596601790464, 521379729431927230596982505472, 2718439710596877006554529792, 152721332056004326210928640, 1769236876958615474372148723712, 4128566676580650285235437568,
    521379729431927230596982505472, 4128566676580650285235437568, 4128566676580650285235437568, 2718439710596877006554529792, 152721332056004326210928640, 77545337773360773782352953344,
    77545337773360773782352953344, 521313285735513254688825802752, 1535741914428105841365221376, 86277635642028418054225920, 1768184851765394189159667597312, 2332372083522834901399240704,
    521313285735513254688825802752, 2332372083522834901399240704, 2332372083522834901399240704, 1535741914428105841365221376, 86277635642028418054225920, 2453403729732485364182111223808,
    2453403729732485364182111223808, 74624572993171829696262832128, 77351909642222433114399965184, 77351909642222433114399965184, 74972743629220842898578210816, 106683855718988923922427150336,
    105913235477800402852773888, 5950181768415752969256960, 376488982561868927385898844160, 160853247139505855268913152, 106683853385705200704188055552, 160853247139505855268913152,
    160853247139505855268913152, 105913235477800402852773888, 5950181768415752969256960, 230225777052843618293851881472, 230225723994738450741157953536, 23936887066463592357474336768,
    93019588264428027218592006144, 93019588264428027218592006144, 86114203982789265372670328832, 3597763239173136423925579776
  ]
def negativeScales : Array ℕ := #[
    11, 11, 31, 13, 9, 31,
    14, 31, 14, 14, 13, 9,
    11, 11, 6, 28, 32, 32,
    28, 34, 17, 12, 35, 18,
    34, 18, 18, 17, 12, 11,
    11, 34, 17, 13, 35, 18,
    34, 18, 18, 17, 13, 15,
    15, 10, 11, 11, 9, 48,
    12, 8, 50, 14, 47, 14,
    14, 12, 8, 45, 45, 22,
    12, 12, 10, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11969026716473715, 11969026716473715, 31017743667623897, 13189978948632521, 9036173612553486, 31780223022632694,
    14792841121720145, 31017743667623897, 14792841121720145, 14792841121720145, 13189978948632521, 9036173612553486,
    11965423579303892, 11965423579303892, 6539158811108986, 28678015100720415, 32807195344983114, 32807196052570199,
    28678002718772507, 34718249245694675, 17134837394440060, 12981032075801390, 35480970064991501, 18737699567141241,
    34718249245694675, 18737699567141241, 18737699567141241, 17134837394440060, 12981032075801390, 11969026716473715,
    11969026716473715, 34718065379512986, 17310994349593887, 13157189013514852, 35480111953242155, 18913856527711209,
    34718065379512986, 18913856527711209, 18913856527711209, 17310994349593887, 13157189013514852, 15952627519441893,
    15952627519441893, 10913637433615165, 11965423579303892, 11965423579303892, 9920352861677847, 48429256623899819,
    12453013354466367, 8299208018387279, 50248522398739815, 14055875526996034, 47429256592346621, 14055875526996034,
    14055875526996034, 12453013354466367, 8299208018387279, 45538964124493661, 45538963792008415, 22273222202369600,
    12231521210875705, 12231521210875705, 10120237877341960, 6539158811108986
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
noncomputable def negativeCeiling : ℝ := 4240231139 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 77545337773360773782352953344, coefficient := (-77545337773360773782352953344) }, { argument := 77545337773360773782352953344, coefficient := (-77545337773360773782352953344) }, { argument := 20052151104032829522504056832, coefficient := (-20052151104032829522504056832) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 68033078158203172180157530112, coefficient := (-68033078158203172180157530112) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 20052151104032829522504056832, coefficient := (-20052151104032829522504056832) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 77351909642222433114399965184, coefficient := (-77351909642222433114399965184) }, { argument := 77351909642222433114399965184, coefficient := (-77351909642222433114399965184) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }, { argument := 3961252152958050443305418752, coefficient := (-3961252152958050443305418752) }, { argument := 138633949123552026048285638656, coefficient := (-138633949123552026048285638656) }, { argument := 138634017118250681741692895232, coefficient := (-138634017118250681741692895232) }, { argument := 3961218155608722596601790464, coefficient := (-3961218155608722596601790464) }, { argument := 521379729431927230596982505472, coefficient := (-521379729431927230596982505472) }, { argument := 2718439710596877006554529792, coefficient := (-2718439710596877006554529792) }, { argument := 152721332056004326210928640, coefficient := (-152721332056004326210928640) }, { argument := 1769236876958615474372148723712, coefficient := (-1769236876958615474372148723712) }, { argument := 4128566676580650285235437568, coefficient := (-4128566676580650285235437568) }, { argument := 521379729431927230596982505472, coefficient := (-521379729431927230596982505472) }, { argument := 4128566676580650285235437568, coefficient := (-4128566676580650285235437568) }, { argument := 4128566676580650285235437568, coefficient := (-4128566676580650285235437568) }, { argument := 2718439710596877006554529792, coefficient := (-2718439710596877006554529792) }, { argument := 152721332056004326210928640, coefficient := (-152721332056004326210928640) }, { argument := 77545337773360773782352953344, coefficient := (-77545337773360773782352953344) }, { argument := 77545337773360773782352953344, coefficient := (-77545337773360773782352953344) }, { argument := 521313285735513254688825802752, coefficient := (-521313285735513254688825802752) }, { argument := 1535741914428105841365221376, coefficient := (-1535741914428105841365221376) }, { argument := 86277635642028418054225920, coefficient := (-86277635642028418054225920) }, { argument := 1768184851765394189159667597312, coefficient := (-1768184851765394189159667597312) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 521313285735513254688825802752, coefficient := (-521313285735513254688825802752) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 1535741914428105841365221376, coefficient := (-1535741914428105841365221376) }, { argument := 86277635642028418054225920, coefficient := (-86277635642028418054225920) }, { argument := 2453403729732485364182111223808, coefficient := (-2453403729732485364182111223808) }, { argument := 2453403729732485364182111223808, coefficient := (-2453403729732485364182111223808) }, { argument := 74624572993171829696262832128, coefficient := (-74624572993171829696262832128) }, { argument := 77351909642222433114399965184, coefficient := (-77351909642222433114399965184) }, { argument := 77351909642222433114399965184, coefficient := (-77351909642222433114399965184) }, { argument := 74972743629220842898578210816, coefficient := (-74972743629220842898578210816) }, { argument := 106683855718988923922427150336, coefficient := (-106683855718988923922427150336) }, { argument := 105913235477800402852773888, coefficient := (-105913235477800402852773888) }, { argument := 5950181768415752969256960, coefficient := (-5950181768415752969256960) }, { argument := 376488982561868927385898844160, coefficient := (-376488982561868927385898844160) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 106683853385705200704188055552, coefficient := (-106683853385705200704188055552) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 105913235477800402852773888, coefficient := (-105913235477800402852773888) }, { argument := 5950181768415752969256960, coefficient := (-5950181768415752969256960) }, { argument := 230225777052843618293851881472, coefficient := (-230225777052843618293851881472) }, { argument := 230225723994738450741157953536, coefficient := (-230225723994738450741157953536) }, { argument := 23936887066463592357474336768, coefficient := (-23936887066463592357474336768) }, { argument := 93019588264428027218592006144, coefficient := (-93019588264428027218592006144) }, { argument := 93019588264428027218592006144, coefficient := (-93019588264428027218592006144) }, { argument := 86114203982789265372670328832, coefficient := (-86114203982789265372670328832) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }] }

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

namespace Parent1

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 425725607084903432650349570422734848
def positiveArguments : Array ℕ := #[
    13595, 93, 1113, 1665, 483, 93,
    1929, 969, 93, 1113, 93, 2295,
    1785, 255, 2397, 28305, 1989, 1785,
    28305, 255, 1989, 1989, 1989, 1989,
    1989, 2295, 2397, 3965, 16653, 72163,
    2379, 2379, 5551, 72163, 72163, 2379,
    890539, 35685, 16653, 72163, 5551, 35685,
    5551, 72163, 72163, 2379, 381, 7239,
    11049, 113919, 3429, 11049, 3429, 3429,
    293751, 3429, 113919, 293751, 381, 3429,
    3429
  ]
def positiveCoefficients : Array ℕ := #[
    4308427477525694678336920019271680, 7195526478346272847851159552, 172228407965578530745340657664, 128823135338134884856690114560, 149481259743709668194069250048, 7195526478346272847851159552,
    149249145986343659392525664256, 149945487258441685797156421632, 7195526478346272847851159552, 172228407965578530745340657664, 7195526478346272847851159552, 355134048769993466361686261760,
    276215371265550473836867092480, 315674710017771970099276677120, 370917784270882064866650095616, 4379986601496586085127463895040, 9849050952554485467097432326144, 276215371265550473836867092480,
    4379986601496586085127463895040, 315674710017771970099276677120, 307782842267327670846794760192, 307782842267327670846794760192, 307782842267327670846794760192, 9849050952554485467097432326144,
    307782842267327670846794760192, 355134048769993466361686261760, 370917784270882064866650095616, 153388507992704149686719610880, 2576926934277429714736889462784, 5583341690934431048596593836032,
    184066209591244979624063533056, 2945059353459919673985016528896, 214743911189785809561407455232, 5583341690934431048596593836032, 5583341690934431048596593836032, 2945059353459919673985016528896,
    68902117790322704039274449207296, 5521986287737349388721905991680, 2576926934277429714736889462784, 5583341690934431048596593836032, 214743911189785809561407455232, 5521986287737349388721905991680,
    214743911189785809561407455232, 5583341690934431048596593836032, 5583341690934431048596593836032, 184066209591244979624063533056, 471655154967729884736566329344, 560090496524179238124672516096,
    427437484189505208042513235968, 4407027854229726110507291639808, 530612049338696120328637120512, 427437484189505208042513235968, 530612049338696120328637120512, 530612049338696120328637120512,
    22727882780007483820743289995264, 530612049338696120328637120512, 4407027854229726110507291639808, 22727882780007483820743289995264, 471655154967729884736566329344, 530612049338696120328637120512,
    530612049338696120328637120512
  ]
def positiveScales : Array ℕ := #[
    13, 6, 10, 10, 8, 6,
    10, 9, 6, 10, 6, 11,
    10, 7, 11, 14, 10, 10,
    14, 7, 10, 10, 10, 10,
    10, 11, 11, 11, 14, 16,
    11, 11, 12, 16, 16, 11,
    19, 15, 14, 16, 12, 15,
    12, 16, 16, 11, 8, 12,
    13, 16, 11, 13, 11, 11,
    18, 11, 16, 18, 8, 11,
    11
  ]
def negativeArguments : Array ℕ := #[
    3, 51, 793
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 32325090305819849738165931737088, 125655865747623239423360705232896
  ]
def negativeScales : Array ℕ := #[
    1, 5, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13730788530903005, 6539158811107971, 10120237877341959, 10701306461953989, 8915879378478017, 6539158811107971,
    10913637427705176, 9920352855028171, 6539158811107971, 10120237877341959, 6539158811107971, 11164278438301170,
    10801708358875019, 7994353435525111, 11227014193649132, 14788769303177175, 10957827560099917, 10801708358875019,
    14788769303177175, 7994353435525111, 10957827560099917, 10957827560099917, 10957827560099917, 10957827560099917,
    10957827560099917, 11164278438301170, 11227014193649132, 11953105149913328, 14023494478482738, 16138971695902674,
    11216139556425134, 11216139556425134, 12438531977761580, 16138971695902674, 16138971695902674, 11216139556425134,
    19764319268085571, 15123030152033653, 14023494478482738, 16138971695902674, 12438531977761580, 15123030152033653,
    12438531977761580, 16138971695902674, 16138971695902674, 11216139556425134, 8573647187493154, 12821574700875186,
    13431628182620892, 16797648861653274, 11743572188923520, 13431628182620892, 11743572188923520, 11743572188923520,
    18164234237408356, 11743572188923520, 16797648861653274, 18164234237408356, 8573647187493154, 11743572188923520,
    11743572188923520
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 5672425342008812, 9631177055717079
  ]

abbrev PositiveTerm := Fin 61
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 37804455729 / 50000000000
noncomputable def negativeCeiling : ℝ := 16792693997 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4308427477525694678336920019271680, coefficient := 4308427477525694678336920019271680 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 172228407965578530745340657664, coefficient := 172228407965578530745340657664 }, { argument := 128823135338134884856690114560, coefficient := 128823135338134884856690114560 }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 149249145986343659392525664256, coefficient := 149249145986343659392525664256 }, { argument := 149945487258441685797156421632, coefficient := 149945487258441685797156421632 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 172228407965578530745340657664, coefficient := 172228407965578530745340657664 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 355134048769993466361686261760, coefficient := 355134048769993466361686261760 }, { argument := 276215371265550473836867092480, coefficient := 276215371265550473836867092480 }, { argument := 315674710017771970099276677120, coefficient := 315674710017771970099276677120 }, { argument := 370917784270882064866650095616, coefficient := 370917784270882064866650095616 }, { argument := 4379986601496586085127463895040, coefficient := 4379986601496586085127463895040 }, { argument := 9849050952554485467097432326144, coefficient := 9849050952554485467097432326144 }, { argument := 276215371265550473836867092480, coefficient := 276215371265550473836867092480 }, { argument := 4379986601496586085127463895040, coefficient := 4379986601496586085127463895040 }, { argument := 315674710017771970099276677120, coefficient := 315674710017771970099276677120 }, { argument := 307782842267327670846794760192, coefficient := 307782842267327670846794760192 }, { argument := 307782842267327670846794760192, coefficient := 307782842267327670846794760192 }, { argument := 307782842267327670846794760192, coefficient := 307782842267327670846794760192 }, { argument := 9849050952554485467097432326144, coefficient := 9849050952554485467097432326144 }, { argument := 307782842267327670846794760192, coefficient := 307782842267327670846794760192 }, { argument := 355134048769993466361686261760, coefficient := 355134048769993466361686261760 }, { argument := 370917784270882064866650095616, coefficient := 370917784270882064866650095616 }, { argument := 32325090305819849738165931737088, coefficient := (-32325090305819849738165931737088) }, { argument := 153388507992704149686719610880, coefficient := 153388507992704149686719610880 }, { argument := 2576926934277429714736889462784, coefficient := 2576926934277429714736889462784 }, { argument := 5583341690934431048596593836032, coefficient := 5583341690934431048596593836032 }, { argument := 184066209591244979624063533056, coefficient := 184066209591244979624063533056 }, { argument := 2945059353459919673985016528896, coefficient := 2945059353459919673985016528896 }, { argument := 214743911189785809561407455232, coefficient := 214743911189785809561407455232 }, { argument := 5583341690934431048596593836032, coefficient := 5583341690934431048596593836032 }, { argument := 5583341690934431048596593836032, coefficient := 5583341690934431048596593836032 }, { argument := 2945059353459919673985016528896, coefficient := 2945059353459919673985016528896 }, { argument := 68902117790322704039274449207296, coefficient := 68902117790322704039274449207296 }, { argument := 5521986287737349388721905991680, coefficient := 5521986287737349388721905991680 }, { argument := 2576926934277429714736889462784, coefficient := 2576926934277429714736889462784 }, { argument := 5583341690934431048596593836032, coefficient := 5583341690934431048596593836032 }, { argument := 214743911189785809561407455232, coefficient := 214743911189785809561407455232 }, { argument := 5521986287737349388721905991680, coefficient := 5521986287737349388721905991680 }, { argument := 214743911189785809561407455232, coefficient := 214743911189785809561407455232 }, { argument := 5583341690934431048596593836032, coefficient := 5583341690934431048596593836032 }, { argument := 5583341690934431048596593836032, coefficient := 5583341690934431048596593836032 }, { argument := 184066209591244979624063533056, coefficient := 184066209591244979624063533056 }, { argument := 125655865747623239423360705232896, coefficient := (-125655865747623239423360705232896) }, { argument := 471655154967729884736566329344, coefficient := 471655154967729884736566329344 }, { argument := 560090496524179238124672516096, coefficient := 560090496524179238124672516096 }, { argument := 427437484189505208042513235968, coefficient := 427437484189505208042513235968 }, { argument := 4407027854229726110507291639808, coefficient := 4407027854229726110507291639808 }, { argument := 530612049338696120328637120512, coefficient := 530612049338696120328637120512 }, { argument := 427437484189505208042513235968, coefficient := 427437484189505208042513235968 }, { argument := 530612049338696120328637120512, coefficient := 530612049338696120328637120512 }, { argument := 530612049338696120328637120512, coefficient := 530612049338696120328637120512 }, { argument := 22727882780007483820743289995264, coefficient := 22727882780007483820743289995264 }, { argument := 530612049338696120328637120512, coefficient := 530612049338696120328637120512 }, { argument := 4407027854229726110507291639808, coefficient := 4407027854229726110507291639808 }, { argument := 22727882780007483820743289995264, coefficient := 22727882780007483820743289995264 }, { argument := 471655154967729884736566329344, coefficient := 471655154967729884736566329344 }, { argument := 530612049338696120328637120512, coefficient := 530612049338696120328637120512 }, { argument := 530612049338696120328637120512, coefficient := 530612049338696120328637120512 }] }

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

end TermShard9


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
