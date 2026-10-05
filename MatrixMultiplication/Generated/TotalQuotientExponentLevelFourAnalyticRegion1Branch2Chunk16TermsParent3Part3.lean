import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 16, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-844045994180245865915182772912128)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4517499105, 180311390595, 4517499105, 113174145, 31806723, 1174579965,
    9396637419, 254456085, 4401719, 702722083, 28048438537, 702722083,
    17604867, 31806723, 1174579965, 9396637419, 254456085, 652747501,
    2335161087, 163186821, 27160443, 2283901061, 1141950255, 13580497,
    57222347, 9135387079, 364629700981, 9135387079, 228863271, 31806723,
    1174579965, 9396637419, 254456085, 57222347, 9135387079, 364629700981,
    9135387079, 228863271, 31806723, 1174579965, 9396637419, 254456085,
    13539246553, 48435760611, 3384810513, 31806723, 1174579965, 9396637419,
    254456085, 6801207833, 24330871971, 1700301393, 27578883, 654779769,
    227268405, 6014125869, 7492365, 17482185, 227268405, 227268405,
    7492365, 2804641965, 112385475, 654779769
  ]
def negativeCoefficients : Array ℕ := #[
    166666299686293906910462607360, 1663079037940322216007444725760, 166666299686293906910462607360, 1043847244287947741237084160, 2346921916017485162817257472, 86668704033846890229147893760,
    86668682810867833426308759552, 2346943138996541965656391680, 40598691938692366914813952, 6481467210022540824295768064, 64675295919901419511400628224, 6481467210022540824295768064,
    40594059500086856603664384, 2346921916017485162817257472, 86668704033846890229147893760, 86668682810867833426308759552, 2346943138996541965656391680, 752566630981279351073406976,
    2692257433923400292118822912, 752566380797312851387613184, 250510870474788037610962944, 21065269180970353570808332288, 21065264098892361263826862080, 250515952552780344592433152,
    1055565990406001539785162752, 168518147460586061431689969664, 1681557693917436907296416333824, 168518147460586061431689969664, 1055445547002258271695273984, 2346921916017485162817257472,
    86668704033846890229147893760, 86668682810867833426308759552, 2346943138996541965656391680, 1055565990406001539785162752, 168518147460586061431689969664, 1681557693917436907296416333824,
    168518147460586061431689969664, 1055445547002258271695273984, 75101501312559525210152239104, 2773398529083100487332732600320, 2773397849947770669641880305664, 75102180447889342901004533760,
    15609688507127826540006473728, 55842630000411173801045262336, 15609683317828134304588234752, 2346921916017485162817257472, 86668704033846890229147893760, 86668682810867833426308759552,
    2346943138996541965656391680, 15682517535932466477207126016, 56103171042403760926089019392, 15682512322421422645045100544, 63592574567472387500015616, 6039277411692829590109028352,
    1048090525768793057258373120, 55470520366259528583088177152, 552838958647275458773647360, 40311174068030502202245120, 1048090525768793057258373120, 1048090525768793057258373120,
    552838958647275458773647360, 12934128136685215420891791360, 1036573047463641485200588800, 6039277411692829590109028352
  ]
def negativeScales : Array ℕ := #[
    32, 37, 32, 26, 24, 30,
    33, 27, 22, 29, 34, 29,
    24, 24, 30, 33, 27, 29,
    31, 27, 24, 31, 30, 23,
    25, 33, 38, 33, 27, 24,
    30, 33, 27, 25, 33, 38,
    33, 27, 24, 30, 33, 27,
    33, 35, 31, 24, 30, 33,
    27, 32, 34, 30, 24, 29,
    27, 32, 22, 24, 27, 27,
    22, 31, 26, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32072877169251634, 37391699581051780, 32072877169251634, 26753969166800896, 24922828411531762, 30129497788861997,
    33129497435582336, 27922841457620549, 22069635617723515, 29388378994979568, 34707201406865376, 29388378994979568,
    24069470992283627, 24922828411531762, 30129497788861997, 33129497435582336, 27922841457620549, 29281949788386448,
    31120874929146053, 27281949308775457, 24695003675106339, 31088853008235029, 30088852660179206, 23695032942556270,
    25770075336211188, 33088818713120656, 38407641124920806, 33088818713120656, 27769910710770090, 24922828411531762,
    30129497788861997, 33129497435582336, 27922841457620549, 25770075336211188, 33088818713120656, 38407641124920806,
    33088818713120656, 27769910710770090, 24922828411531762, 30129497788861997, 33129497435582336, 27922841457620549,
    33656428405352591, 35495353546087357, 31656427925741600, 24922828411531762, 30129497788861997, 33129497435582336,
    27922841457620549, 32663143832723161, 34502068973453393, 30663143353112169, 24717060690315519, 29286434506057161,
    27759821893079443, 32485707916225222, 22836989754671989, 24059382174660044, 27759821893079443, 27759821893079443,
    22836989754671989, 31385169465003044, 26743880349128728, 29286434506057161
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
noncomputable def negativeCeiling : ℝ := 2642243993 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 166666299686293906910462607360, coefficient := (-166666299686293906910462607360) }, { argument := 1663079037940322216007444725760, coefficient := (-1663079037940322216007444725760) }, { argument := 166666299686293906910462607360, coefficient := (-166666299686293906910462607360) }, { argument := 1043847244287947741237084160, coefficient := (-1043847244287947741237084160) }, { argument := 2346921916017485162817257472, coefficient := (-2346921916017485162817257472) }, { argument := 86668704033846890229147893760, coefficient := (-86668704033846890229147893760) }, { argument := 86668682810867833426308759552, coefficient := (-86668682810867833426308759552) }, { argument := 2346943138996541965656391680, coefficient := (-2346943138996541965656391680) }, { argument := 40598691938692366914813952, coefficient := (-40598691938692366914813952) }, { argument := 6481467210022540824295768064, coefficient := (-6481467210022540824295768064) }, { argument := 64675295919901419511400628224, coefficient := (-64675295919901419511400628224) }, { argument := 6481467210022540824295768064, coefficient := (-6481467210022540824295768064) }, { argument := 40594059500086856603664384, coefficient := (-40594059500086856603664384) }, { argument := 2346921916017485162817257472, coefficient := (-2346921916017485162817257472) }, { argument := 86668704033846890229147893760, coefficient := (-86668704033846890229147893760) }, { argument := 86668682810867833426308759552, coefficient := (-86668682810867833426308759552) }, { argument := 2346943138996541965656391680, coefficient := (-2346943138996541965656391680) }, { argument := 752566630981279351073406976, coefficient := (-752566630981279351073406976) }, { argument := 2692257433923400292118822912, coefficient := (-2692257433923400292118822912) }, { argument := 752566380797312851387613184, coefficient := (-752566380797312851387613184) }, { argument := 250510870474788037610962944, coefficient := (-250510870474788037610962944) }, { argument := 21065269180970353570808332288, coefficient := (-21065269180970353570808332288) }, { argument := 21065264098892361263826862080, coefficient := (-21065264098892361263826862080) }, { argument := 250515952552780344592433152, coefficient := (-250515952552780344592433152) }, { argument := 1055565990406001539785162752, coefficient := (-1055565990406001539785162752) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1681557693917436907296416333824, coefficient := (-1681557693917436907296416333824) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1055445547002258271695273984, coefficient := (-1055445547002258271695273984) }, { argument := 2346921916017485162817257472, coefficient := (-2346921916017485162817257472) }, { argument := 86668704033846890229147893760, coefficient := (-86668704033846890229147893760) }, { argument := 86668682810867833426308759552, coefficient := (-86668682810867833426308759552) }, { argument := 2346943138996541965656391680, coefficient := (-2346943138996541965656391680) }, { argument := 1055565990406001539785162752, coefficient := (-1055565990406001539785162752) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1681557693917436907296416333824, coefficient := (-1681557693917436907296416333824) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1055445547002258271695273984, coefficient := (-1055445547002258271695273984) }, { argument := 75101501312559525210152239104, coefficient := (-75101501312559525210152239104) }, { argument := 2773398529083100487332732600320, coefficient := (-2773398529083100487332732600320) }, { argument := 2773397849947770669641880305664, coefficient := (-2773397849947770669641880305664) }, { argument := 75102180447889342901004533760, coefficient := (-75102180447889342901004533760) }, { argument := 15609688507127826540006473728, coefficient := (-15609688507127826540006473728) }, { argument := 55842630000411173801045262336, coefficient := (-55842630000411173801045262336) }, { argument := 15609683317828134304588234752, coefficient := (-15609683317828134304588234752) }, { argument := 2346921916017485162817257472, coefficient := (-2346921916017485162817257472) }, { argument := 86668704033846890229147893760, coefficient := (-86668704033846890229147893760) }, { argument := 86668682810867833426308759552, coefficient := (-86668682810867833426308759552) }, { argument := 2346943138996541965656391680, coefficient := (-2346943138996541965656391680) }, { argument := 15682517535932466477207126016, coefficient := (-15682517535932466477207126016) }, { argument := 56103171042403760926089019392, coefficient := (-56103171042403760926089019392) }, { argument := 15682512322421422645045100544, coefficient := (-15682512322421422645045100544) }, { argument := 63592574567472387500015616, coefficient := (-63592574567472387500015616) }, { argument := 6039277411692829590109028352, coefficient := (-6039277411692829590109028352) }, { argument := 1048090525768793057258373120, coefficient := (-1048090525768793057258373120) }, { argument := 55470520366259528583088177152, coefficient := (-55470520366259528583088177152) }, { argument := 552838958647275458773647360, coefficient := (-552838958647275458773647360) }, { argument := 40311174068030502202245120, coefficient := (-40311174068030502202245120) }, { argument := 1048090525768793057258373120, coefficient := (-1048090525768793057258373120) }, { argument := 1048090525768793057258373120, coefficient := (-1048090525768793057258373120) }, { argument := 552838958647275458773647360, coefficient := (-552838958647275458773647360) }, { argument := 12934128136685215420891791360, coefficient := (-12934128136685215420891791360) }, { argument := 1036573047463641485200588800, coefficient := (-1036573047463641485200588800) }, { argument := 6039277411692829590109028352, coefficient := (-6039277411692829590109028352) }] }

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


end Parent3

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 15290318056394707431222662955794432
def positiveArguments : Array ℕ := #[
    1739, 217, 2597, 3885, 1127, 217,
    4501, 2261, 217, 2597, 217, 1305,
    1015, 145, 1363, 16095, 1131, 1015,
    16095, 145
  ]
def positiveCoefficients : Array ℕ := #[
    137777774612305683075172929634304, 8394780891403984989159686144, 200933142626508285869564100608, 150293657894490698999471800320, 174394803034327946226414125056, 8394780891403984989159686144,
    174124003650734269291279941632, 174936401801515300096682491904, 8394780891403984989159686144, 200933142626508285869564100608, 8394780891403984989159686144, 403877937816855314685839278080,
    314127284968665244755652771840, 359002611392760279720746024960, 421828068386493328671876579328, 4981161233074548881125351096320, 11200881475454120727287275978752, 314127284968665244755652771840,
    4981161233074548881125351096320, 359002611392760279720746024960
  ]
def positiveScales : Array ℕ := #[
    10, 7, 11, 11, 10, 7,
    12, 11, 7, 11, 7, 10,
    9, 7, 10, 13, 10, 9,
    13, 7
  ]
def negativeArguments : Array ℕ := #[
    227268405, 17482185, 112385475, 17482185, 227268405, 227268405,
    3759327, 39509823, 26692701, 21725294691, 420058821, 12643911,
    21725289381, 12643911, 12643911, 1083161709, 12643911, 420058821,
    1083161709, 316081239, 12643911, 12643911, 26692701, 695817271,
    383320953, 21534885, 377137389, 1164319449, 347908527, 1164319449,
    1164319449, 383320953, 21534885, 38331179, 1415519445, 11324152787,
    306652205, 7811913641, 27946605267, 1952977761, 652747501, 2335161087,
    163186821, 7
  ]
def negativeCoefficients : Array ℕ := #[
    1048090525768793057258373120, 40311174068030502202245120, 1036573047463641485200588800, 40311174068030502202245120, 1048090525768793057258373120, 1048090525768793057258373120,
    69347343058386307547922432, 2915310373114253351030095872, 246196711991525511064977408, 100190237772699458599768817664, 1937179391722792837063901184, 233238990307761010482610176,
    100190213284646700750339047424, 233238990307761010482610176, 233238990307761010482610176, 9990403418182429949005135872, 233238990307761010482610176, 1937179391722792837063901184,
    9990403418182429949005135872, 2915334861167011200459866112, 233238990307761010482610176, 233238990307761010482610176, 246196711991525511064977408, 802222695012750190754922496,
    883877939760180946330976256, 49656064031470839681515520, 3478478447755021920409485312, 1342368930984095032723636224, 802222444828783691069128704, 1342368930984095032723636224,
    1342368930984095032723636224, 883877939760180946330976256, 49656064031470839681515520, 2828341796226200068010541056, 104446899733097534378716692480, 104446874156686876180423376896,
    2828367372636858266303856640, 18013046457680944467627999232, 64440484386166548927489245184, 18013040469406649539664805888, 752566630981279351073406976, 2692257433923400292118822912,
    752566380797312851387613184, 1109194275199700726309615304704
  ]
def negativeScales : Array ℕ := #[
    27, 24, 26, 24, 27, 27,
    21, 25, 24, 34, 28, 23,
    34, 23, 23, 30, 23, 28,
    30, 28, 23, 23, 24, 29,
    28, 24, 28, 30, 28, 30,
    30, 28, 24, 25, 30, 33,
    28, 32, 34, 30, 29, 31,
    27, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10764042217287691, 7761551232426566, 11342630298678407, 11923698882884927, 10138271800172220, 7761551232426566,
    12136029849385551, 11142745276751528, 7761551232426566, 11342630298678407, 7761551232426566, 10349834091457246,
    9987264010882511, 7179909090014934, 10412569846805208, 13974324955400894, 10143383213989820, 9987264010882511,
    13974324955400894, 7179909090014934
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    27759821893079443, 24059382174660044, 26743880349128728, 24059382174660044, 27759821893079443, 27759821893079443,
    21842042982536767, 25235708047414131, 24669941961564168, 34338656695366042, 28646016122302828, 23591939449532307,
    34338656342748888, 23591939449532307, 23591939449532307, 30012601498000512, 23591939449532307, 28646016122302828,
    30012601498000512, 28235720165727235, 23591939449532307, 23591939449532307, 24669941961564168, 29374133247882541,
    28513977619651006, 24360172283571542, 28490514943922275, 30116839792180295, 28374132797958565, 30116839792180295,
    30116839792180295, 28513977619651006, 24360172283571542, 25192015037807678, 30398684421677392, 33398684068397731,
    28192028083894976, 32863028856836993, 34701953995455768, 30863028377225982, 29281949788386448, 31120874929146053,
    27281949308775457, 2807354922807594
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 44
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
noncomputable def positiveFloor : ℝ := 21285388559 / 1000000000000
noncomputable def negativeCeiling : ℝ := 52166937 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1048090525768793057258373120, coefficient := (-1048090525768793057258373120) }, { argument := 40311174068030502202245120, coefficient := (-40311174068030502202245120) }, { argument := 1036573047463641485200588800, coefficient := (-1036573047463641485200588800) }, { argument := 40311174068030502202245120, coefficient := (-40311174068030502202245120) }, { argument := 1048090525768793057258373120, coefficient := (-1048090525768793057258373120) }, { argument := 1048090525768793057258373120, coefficient := (-1048090525768793057258373120) }, { argument := 69347343058386307547922432, coefficient := (-69347343058386307547922432) }, { argument := 2915310373114253351030095872, coefficient := (-2915310373114253351030095872) }, { argument := 246196711991525511064977408, coefficient := (-246196711991525511064977408) }, { argument := 100190237772699458599768817664, coefficient := (-100190237772699458599768817664) }, { argument := 1937179391722792837063901184, coefficient := (-1937179391722792837063901184) }, { argument := 233238990307761010482610176, coefficient := (-233238990307761010482610176) }, { argument := 100190213284646700750339047424, coefficient := (-100190213284646700750339047424) }, { argument := 233238990307761010482610176, coefficient := (-233238990307761010482610176) }, { argument := 233238990307761010482610176, coefficient := (-233238990307761010482610176) }, { argument := 9990403418182429949005135872, coefficient := (-9990403418182429949005135872) }, { argument := 233238990307761010482610176, coefficient := (-233238990307761010482610176) }, { argument := 1937179391722792837063901184, coefficient := (-1937179391722792837063901184) }, { argument := 9990403418182429949005135872, coefficient := (-9990403418182429949005135872) }, { argument := 2915334861167011200459866112, coefficient := (-2915334861167011200459866112) }, { argument := 233238990307761010482610176, coefficient := (-233238990307761010482610176) }, { argument := 233238990307761010482610176, coefficient := (-233238990307761010482610176) }, { argument := 246196711991525511064977408, coefficient := (-246196711991525511064977408) }, { argument := 802222695012750190754922496, coefficient := (-802222695012750190754922496) }, { argument := 883877939760180946330976256, coefficient := (-883877939760180946330976256) }, { argument := 49656064031470839681515520, coefficient := (-49656064031470839681515520) }, { argument := 3478478447755021920409485312, coefficient := (-3478478447755021920409485312) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 802222444828783691069128704, coefficient := (-802222444828783691069128704) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 883877939760180946330976256, coefficient := (-883877939760180946330976256) }, { argument := 49656064031470839681515520, coefficient := (-49656064031470839681515520) }, { argument := 2828341796226200068010541056, coefficient := (-2828341796226200068010541056) }, { argument := 104446899733097534378716692480, coefficient := (-104446899733097534378716692480) }, { argument := 104446874156686876180423376896, coefficient := (-104446874156686876180423376896) }, { argument := 2828367372636858266303856640, coefficient := (-2828367372636858266303856640) }, { argument := 18013046457680944467627999232, coefficient := (-18013046457680944467627999232) }, { argument := 64440484386166548927489245184, coefficient := (-64440484386166548927489245184) }, { argument := 18013040469406649539664805888, coefficient := (-18013040469406649539664805888) }, { argument := 752566630981279351073406976, coefficient := (-752566630981279351073406976) }, { argument := 2692257433923400292118822912, coefficient := (-2692257433923400292118822912) }, { argument := 752566380797312851387613184, coefficient := (-752566380797312851387613184) }, { argument := 137777774612305683075172929634304, coefficient := 137777774612305683075172929634304 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 200933142626508285869564100608, coefficient := 200933142626508285869564100608 }, { argument := 150293657894490698999471800320, coefficient := 150293657894490698999471800320 }, { argument := 174394803034327946226414125056, coefficient := 174394803034327946226414125056 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 174124003650734269291279941632, coefficient := 174124003650734269291279941632 }, { argument := 174936401801515300096682491904, coefficient := 174936401801515300096682491904 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 200933142626508285869564100608, coefficient := 200933142626508285869564100608 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 403877937816855314685839278080, coefficient := 403877937816855314685839278080 }, { argument := 314127284968665244755652771840, coefficient := 314127284968665244755652771840 }, { argument := 359002611392760279720746024960, coefficient := 359002611392760279720746024960 }, { argument := 421828068386493328671876579328, coefficient := 421828068386493328671876579328 }, { argument := 4981161233074548881125351096320, coefficient := 4981161233074548881125351096320 }, { argument := 11200881475454120727287275978752, coefficient := 11200881475454120727287275978752 }, { argument := 314127284968665244755652771840, coefficient := 314127284968665244755652771840 }, { argument := 4981161233074548881125351096320, coefficient := 4981161233074548881125351096320 }, { argument := 359002611392760279720746024960, coefficient := 359002611392760279720746024960 }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16
