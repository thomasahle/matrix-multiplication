import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1809169067822223451311537691557888)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8699280359045, 81944737743227, 455, 403, 18863, 5135,
    40972380932571, 18863, 455, 455, 195, 455,
    5135, 195, 4349628118565, 403, 6256355322117, 258363492133839,
    15835652847, 1326695125325525, 16249656843, 517504995, 15835652847, 9004586913,
    16249656843, 253680948549, 310502997, 129181792699817, 15835652847, 517504995,
    310502997, 517504995, 7969576923, 9004586913, 6256355322117, 25090137,
    2109810599, 1054905045, 12545323, 17788465, 1313631595, 13691762425,
    1313631595, 17788465, 22615147626293, 398337079, 340799874024351, 9856723891,
    313584509, 340800033031865, 161029883, 161029883, 5449590251, 296633995,
    9856723891, 5449590251, 22614966168603, 313584509, 296633995, 398337079,
    5804657, 428658731, 4467838265, 428658731
  ]
def negativeCoefficients : Array ℕ := #[
    19589037891693268326059868160, 184523145182685068265621815296, 17601959933589000783721922560, 15590307369750257837010845696, 729726967532504003919443132416, 198650690679075865987718840320,
    184523199500408770997010825216, 729726967532504003919443132416, 17601959933589000783721922560, 17601959933589000783721922560, 15087394228790572100333076480, 17601959933589000783721922560,
    198650690679075865987718840320, 15087394228790572100333076480, 19588983573969565594670858240, 15590307369750257837010845696, 28176119497383540671782060032, 1163565726900097394859671814144,
    584232470617438077798007701504, 5974903672050287880731780710400, 599506522136848223622792216576, 19092564399262682280980643840, 584232470617438077798007701504, 332210620547170671689063202816,
    599506522136848223622792216576, 9359175068518566854136711610368, 366577236465843499794828361728, 1163566146931897003272740798464, 584232470617438077798007701504, 19092564399262682280980643840,
    366577236465843499794828361728, 19092564399262682280980643840, 588050983497290614254203830272, 332210620547170671689063202816, 28176119497383540671782060032, 115707834003327687063502848,
    9729784040938212311743594496, 9729781693590028932203151360, 115710181351511066603945984, 328139261319139779086909440, 48464451680207751712121815040, 505136874744015738359093657600,
    48464451680207751712121815040, 328139261319139779086909440, 50924785211350955963831025664, 7348022151382023485117169664, 1534826185663979142643602948096, 181824463022495602408324857856,
    5784613183002869552113516544, 1534826901770159942152528855040, 5940954079840784945413881856, 5940954079840784945413881856, 100527196666779597892134895616, 5471931389327038765512785920,
    181824463022495602408324857856, 100527196666779597892134895616, 50924376604958422208341868544, 5784613183002869552113516544, 5471931389327038765512785920, 7348022151382023485117169664,
    13384627764333333094334464, 1976839476429526714573389824, 20604267259295378801489346560, 1976839476429526714573389824
  ]
def negativeScales : Array ℕ := #[
    42, 46, 8, 8, 14, 12,
    45, 14, 8, 8, 7, 8,
    12, 7, 41, 8, 42, 47,
    33, 50, 33, 28, 33, 33,
    33, 37, 28, 46, 33, 28,
    28, 28, 32, 33, 42, 24,
    30, 29, 23, 24, 30, 33,
    30, 24, 44, 28, 48, 33,
    28, 48, 27, 27, 32, 28,
    33, 32, 44, 28, 28, 28,
    22, 28, 32, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    42984033217074251, 46219716540084265, 8829722736256263, 8654636028551931, 14203271522207837, 12326148561205558,
    45219716964767570, 14203271522207837, 8829722736256263, 8829722736256263, 7607330313756529, 8829722736256263,
    12326148561205558, 7607330313756529, 41984029216671424, 8654636028551931, 42508459589736904, 47876395556721475,
    33882457297770502, 50236758300638843, 33919690206981930, 28946997556694945, 33882457297770502, 33068012947748463,
    33919690206981930, 37884224224049136, 28210031952620891, 46876396077515189, 33882457297770502, 28946997556694945,
    28210031952620891, 28946997556694945, 32891855996366156, 33068012947748463, 42508459589736904, 24580617012549822,
    30974466361404519, 29974466013348606, 23580646279999710, 24084438687327386, 30290913585820016, 33672589113414427,
    30290913585820016, 24084438687327386, 44362354647105111, 28569414537572205, 48275918130699038, 33198461067365416,
    28224279051521148, 48275918803819294, 27262753199335783, 27262753199335783, 32343500613220146, 28144108702837164,
    33198461067365416, 32343500613220146, 44362343071272660, 28224279051521148, 28144108702837164, 28569414537572205,
    22468779389383406, 28675254287915937, 32056929815432888, 28675254287915937
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
noncomputable def negativeCeiling : ℝ := 880482101 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 19589037891693268326059868160, coefficient := (-19589037891693268326059868160) }, { argument := 184523145182685068265621815296, coefficient := (-184523145182685068265621815296) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 15590307369750257837010845696, coefficient := (-15590307369750257837010845696) }, { argument := 729726967532504003919443132416, coefficient := (-729726967532504003919443132416) }, { argument := 198650690679075865987718840320, coefficient := (-198650690679075865987718840320) }, { argument := 184523199500408770997010825216, coefficient := (-184523199500408770997010825216) }, { argument := 729726967532504003919443132416, coefficient := (-729726967532504003919443132416) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 15087394228790572100333076480, coefficient := (-15087394228790572100333076480) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 198650690679075865987718840320, coefficient := (-198650690679075865987718840320) }, { argument := 15087394228790572100333076480, coefficient := (-15087394228790572100333076480) }, { argument := 19588983573969565594670858240, coefficient := (-19588983573969565594670858240) }, { argument := 15590307369750257837010845696, coefficient := (-15590307369750257837010845696) }, { argument := 28176119497383540671782060032, coefficient := (-28176119497383540671782060032) }, { argument := 1163565726900097394859671814144, coefficient := (-1163565726900097394859671814144) }, { argument := 584232470617438077798007701504, coefficient := (-584232470617438077798007701504) }, { argument := 5974903672050287880731780710400, coefficient := (-5974903672050287880731780710400) }, { argument := 599506522136848223622792216576, coefficient := (-599506522136848223622792216576) }, { argument := 19092564399262682280980643840, coefficient := (-19092564399262682280980643840) }, { argument := 584232470617438077798007701504, coefficient := (-584232470617438077798007701504) }, { argument := 332210620547170671689063202816, coefficient := (-332210620547170671689063202816) }, { argument := 599506522136848223622792216576, coefficient := (-599506522136848223622792216576) }, { argument := 9359175068518566854136711610368, coefficient := (-9359175068518566854136711610368) }, { argument := 366577236465843499794828361728, coefficient := (-366577236465843499794828361728) }, { argument := 1163566146931897003272740798464, coefficient := (-1163566146931897003272740798464) }, { argument := 584232470617438077798007701504, coefficient := (-584232470617438077798007701504) }, { argument := 19092564399262682280980643840, coefficient := (-19092564399262682280980643840) }, { argument := 366577236465843499794828361728, coefficient := (-366577236465843499794828361728) }, { argument := 19092564399262682280980643840, coefficient := (-19092564399262682280980643840) }, { argument := 588050983497290614254203830272, coefficient := (-588050983497290614254203830272) }, { argument := 332210620547170671689063202816, coefficient := (-332210620547170671689063202816) }, { argument := 28176119497383540671782060032, coefficient := (-28176119497383540671782060032) }, { argument := 115707834003327687063502848, coefficient := (-115707834003327687063502848) }, { argument := 9729784040938212311743594496, coefficient := (-9729784040938212311743594496) }, { argument := 9729781693590028932203151360, coefficient := (-9729781693590028932203151360) }, { argument := 115710181351511066603945984, coefficient := (-115710181351511066603945984) }, { argument := 328139261319139779086909440, coefficient := (-328139261319139779086909440) }, { argument := 48464451680207751712121815040, coefficient := (-48464451680207751712121815040) }, { argument := 505136874744015738359093657600, coefficient := (-505136874744015738359093657600) }, { argument := 48464451680207751712121815040, coefficient := (-48464451680207751712121815040) }, { argument := 328139261319139779086909440, coefficient := (-328139261319139779086909440) }, { argument := 50924785211350955963831025664, coefficient := (-50924785211350955963831025664) }, { argument := 7348022151382023485117169664, coefficient := (-7348022151382023485117169664) }, { argument := 1534826185663979142643602948096, coefficient := (-1534826185663979142643602948096) }, { argument := 181824463022495602408324857856, coefficient := (-181824463022495602408324857856) }, { argument := 5784613183002869552113516544, coefficient := (-5784613183002869552113516544) }, { argument := 1534826901770159942152528855040, coefficient := (-1534826901770159942152528855040) }, { argument := 5940954079840784945413881856, coefficient := (-5940954079840784945413881856) }, { argument := 5940954079840784945413881856, coefficient := (-5940954079840784945413881856) }, { argument := 100527196666779597892134895616, coefficient := (-100527196666779597892134895616) }, { argument := 5471931389327038765512785920, coefficient := (-5471931389327038765512785920) }, { argument := 181824463022495602408324857856, coefficient := (-181824463022495602408324857856) }, { argument := 100527196666779597892134895616, coefficient := (-100527196666779597892134895616) }, { argument := 50924376604958422208341868544, coefficient := (-50924376604958422208341868544) }, { argument := 5784613183002869552113516544, coefficient := (-5784613183002869552113516544) }, { argument := 5471931389327038765512785920, coefficient := (-5471931389327038765512785920) }, { argument := 7348022151382023485117169664, coefficient := (-7348022151382023485117169664) }, { argument := 13384627764333333094334464, coefficient := (-13384627764333333094334464) }, { argument := 1976839476429526714573389824, coefficient := (-1976839476429526714573389824) }, { argument := 20604267259295378801489346560, coefficient := (-20604267259295378801489346560) }, { argument := 1976839476429526714573389824, coefficient := (-1976839476429526714573389824) }] }

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
def constantNumerator : ℤ := (-11130423408443266161067653291048960)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5804657, 805937811, 29207453037, 233659710165, 6447416619, 12536559721141,
    17788465, 5804657, 341326576531623, 58608311, 100292471755185, 117403869,
    52616407, 17788465, 5804657, 8698904734075, 81913286989445, 455,
    403, 18863, 5135, 40956655549989, 18863, 455,
    455, 195, 455, 5135, 195, 4349440311771,
    403, 170340488362519, 7095209171410053, 26839293201, 36914431352949255, 27540974069,
    877101085, 26839293201, 15261558879, 27540974069, 429954951867, 526260651,
    3547605861233315, 26839293201, 877101085, 526260651, 877101085, 13507356709,
    15261558879, 170340488362519, 340112630512543, 14435867593, 4918924857561309, 357210936397,
    11364406403, 4918927255797163, 5835776261, 5835776261, 197494954517, 10750114165,
    357210936397, 197494954517, 340110223624017, 11364406403
  ]
def negativeCoefficients : Array ℕ := #[
    13384627764333333094334464, 7433464269421349339595276288, 269391205609214897601323728896, 269391304609431576686666711040, 7433365269204670254252294144, 28229822844319288422425427968,
    328139261319139779086909440, 13384627764333333094334464, 96074890179966526737705074688, 270283128402344081195270144, 28229821151544822558212751360, 270714890588290317746700288,
    242650348501784941903740928, 328139261319139779086909440, 13384627764333333094334464, 19588192059455806799190425600, 184452324381178500056728207360, 17601959933589000783721922560,
    15590307369750257837010845696, 729726967532504003919443132416, 198650690679075865987718840320, 184452378673272217308751724544, 729726967532504003919443132416, 17601959933589000783721922560,
    17601959933589000783721922560, 15087394228790572100333076480, 17601959933589000783721922560, 198650690679075865987718840320, 15087394228790572100333076480, 19588137767362089547166908416,
    15590307369750257837010845696, 95893169989443609844596604928, 3994247672559755046502621249536, 1980390291192399246144269451264, 20780977410717002415808771522560, 2032165200766056742775492182016,
    64718636967071870789028413440, 1980390291192399246144269451264, 1126104283227050551729094393856, 2032165200766056742775492182016, 31725075841258631060781728268288, 1242597829767779919149345538048,
    3994249108676936243784250818560, 1980390291192399246144269451264, 64718636967071870789028413440, 1242597829767779919149345538048, 64718636967071870789028413440, 1993334018585813620302075133952,
    1126104283227050551729094393856, 95893169989443609844596604928, 1531731116040287842775836131328, 266294754970028519467975180288, 44305736311153162652117555478528, 6589378724045599322154364567552,
    209636296465767132347129397248, 44305757912541359494044053405696, 215302142316193271059213975552, 215302142316193271059213975552, 3643138881824007191870383849472, 198304604764914854922960240640,
    6589378724045599322154364567552, 3643138881824007191870383849472, 1531720276378019026853462802432, 209636296465767132347129397248
  ]
def negativeScales : Array ℕ := #[
    22, 29, 34, 37, 32, 43,
    24, 22, 48, 25, 46, 26,
    25, 24, 22, 42, 46, 8,
    8, 14, 12, 45, 14, 8,
    8, 7, 8, 12, 7, 41,
    8, 47, 52, 34, 55, 34,
    29, 34, 33, 34, 38, 28,
    51, 34, 29, 28, 29, 33,
    33, 47, 48, 33, 52, 38,
    33, 52, 32, 32, 37, 33,
    38, 37, 48, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22468779389383406, 29586093278720296, 34765617506222812, 37765618036407515, 32586074064519810, 43511206732059083,
    24084438687327386, 22468779389383406, 48278146079038120, 25804601926638430, 46511206645549245, 26806904712541679,
    25649009399238140, 24084438687327386, 22468779389383406, 42983970921790039, 46219162721043120, 8829722736256263,
    8654636028551931, 14203271522207837, 12326148561205558, 45219163145689018, 14203271522207837, 8829722736256263,
    8829722736256263, 7607330313756529, 8829722736256263, 12326148561205558, 7607330313756529, 41983966923102159,
    8654636028551931, 47275414719500775, 52655766639841882, 34643627628297234, 55035034452941523, 34680860534523946,
    29708167880561462, 34643627628297234, 33829183282593103, 34680860534523946, 38645394554472262, 28971202301153938,
    51655767158557529, 34643627628297234, 29708167880561462, 28971202301153938, 29708167880561462, 33653026326304389,
    33829183282593103, 47275414719500775, 48273005911768027, 33748938764980729, 52127264439654116, 38377985294556592,
    33403803278712329, 52127265143044029, 32442277426526992, 32442277426526992, 37523024840411893, 33323632930028338,
    38377985294556592, 37523024840411893, 48272995702154753, 33403803278712329
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
noncomputable def negativeCeiling : ℝ := 27159947941 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13384627764333333094334464, coefficient := (-13384627764333333094334464) }, { argument := 7433464269421349339595276288, coefficient := (-7433464269421349339595276288) }, { argument := 269391205609214897601323728896, coefficient := (-269391205609214897601323728896) }, { argument := 269391304609431576686666711040, coefficient := (-269391304609431576686666711040) }, { argument := 7433365269204670254252294144, coefficient := (-7433365269204670254252294144) }, { argument := 28229822844319288422425427968, coefficient := (-28229822844319288422425427968) }, { argument := 328139261319139779086909440, coefficient := (-328139261319139779086909440) }, { argument := 13384627764333333094334464, coefficient := (-13384627764333333094334464) }, { argument := 96074890179966526737705074688, coefficient := (-96074890179966526737705074688) }, { argument := 270283128402344081195270144, coefficient := (-270283128402344081195270144) }, { argument := 28229821151544822558212751360, coefficient := (-28229821151544822558212751360) }, { argument := 270714890588290317746700288, coefficient := (-270714890588290317746700288) }, { argument := 242650348501784941903740928, coefficient := (-242650348501784941903740928) }, { argument := 328139261319139779086909440, coefficient := (-328139261319139779086909440) }, { argument := 13384627764333333094334464, coefficient := (-13384627764333333094334464) }, { argument := 19588192059455806799190425600, coefficient := (-19588192059455806799190425600) }, { argument := 184452324381178500056728207360, coefficient := (-184452324381178500056728207360) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 15590307369750257837010845696, coefficient := (-15590307369750257837010845696) }, { argument := 729726967532504003919443132416, coefficient := (-729726967532504003919443132416) }, { argument := 198650690679075865987718840320, coefficient := (-198650690679075865987718840320) }, { argument := 184452378673272217308751724544, coefficient := (-184452378673272217308751724544) }, { argument := 729726967532504003919443132416, coefficient := (-729726967532504003919443132416) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 15087394228790572100333076480, coefficient := (-15087394228790572100333076480) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 198650690679075865987718840320, coefficient := (-198650690679075865987718840320) }, { argument := 15087394228790572100333076480, coefficient := (-15087394228790572100333076480) }, { argument := 19588137767362089547166908416, coefficient := (-19588137767362089547166908416) }, { argument := 15590307369750257837010845696, coefficient := (-15590307369750257837010845696) }, { argument := 95893169989443609844596604928, coefficient := (-95893169989443609844596604928) }, { argument := 3994247672559755046502621249536, coefficient := (-3994247672559755046502621249536) }, { argument := 1980390291192399246144269451264, coefficient := (-1980390291192399246144269451264) }, { argument := 20780977410717002415808771522560, coefficient := (-20780977410717002415808771522560) }, { argument := 2032165200766056742775492182016, coefficient := (-2032165200766056742775492182016) }, { argument := 64718636967071870789028413440, coefficient := (-64718636967071870789028413440) }, { argument := 1980390291192399246144269451264, coefficient := (-1980390291192399246144269451264) }, { argument := 1126104283227050551729094393856, coefficient := (-1126104283227050551729094393856) }, { argument := 2032165200766056742775492182016, coefficient := (-2032165200766056742775492182016) }, { argument := 31725075841258631060781728268288, coefficient := (-31725075841258631060781728268288) }, { argument := 1242597829767779919149345538048, coefficient := (-1242597829767779919149345538048) }, { argument := 3994249108676936243784250818560, coefficient := (-3994249108676936243784250818560) }, { argument := 1980390291192399246144269451264, coefficient := (-1980390291192399246144269451264) }, { argument := 64718636967071870789028413440, coefficient := (-64718636967071870789028413440) }, { argument := 1242597829767779919149345538048, coefficient := (-1242597829767779919149345538048) }, { argument := 64718636967071870789028413440, coefficient := (-64718636967071870789028413440) }, { argument := 1993334018585813620302075133952, coefficient := (-1993334018585813620302075133952) }, { argument := 1126104283227050551729094393856, coefficient := (-1126104283227050551729094393856) }, { argument := 95893169989443609844596604928, coefficient := (-95893169989443609844596604928) }, { argument := 1531731116040287842775836131328, coefficient := (-1531731116040287842775836131328) }, { argument := 266294754970028519467975180288, coefficient := (-266294754970028519467975180288) }, { argument := 44305736311153162652117555478528, coefficient := (-44305736311153162652117555478528) }, { argument := 6589378724045599322154364567552, coefficient := (-6589378724045599322154364567552) }, { argument := 209636296465767132347129397248, coefficient := (-209636296465767132347129397248) }, { argument := 44305757912541359494044053405696, coefficient := (-44305757912541359494044053405696) }, { argument := 215302142316193271059213975552, coefficient := (-215302142316193271059213975552) }, { argument := 215302142316193271059213975552, coefficient := (-215302142316193271059213975552) }, { argument := 3643138881824007191870383849472, coefficient := (-3643138881824007191870383849472) }, { argument := 198304604764914854922960240640, coefficient := (-198304604764914854922960240640) }, { argument := 6589378724045599322154364567552, coefficient := (-6589378724045599322154364567552) }, { argument := 3643138881824007191870383849472, coefficient := (-3643138881824007191870383849472) }, { argument := 1531720276378019026853462802432, coefficient := (-1531720276378019026853462802432) }, { argument := 209636296465767132347129397248, coefficient := (-209636296465767132347129397248) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
