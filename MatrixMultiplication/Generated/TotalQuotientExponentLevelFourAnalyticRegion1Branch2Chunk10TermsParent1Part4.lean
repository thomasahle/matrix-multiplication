import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
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

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-11263423662172966559199439183937536)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    262088445, 423506171, 6427859123, 7706327721, 22391249362463, 1335394253814609,
    28623, 24427283604875377, 708267, 22533, 48853175637225907, 11571,
    11571, 391587, 21315, 708267, 391587, 668393536839949,
    22533, 21315, 28623, 3125790518443375, 5347129040362513, 3125790518004335,
    794503119, 124033, 26994888241, 3069157, 97643, 215959053143,
    50141, 50141, 1696877, 92365, 3069157, 1696877,
    6356077737, 97643, 92365, 124033, 2912745324165, 10575915740465,
    1456372648485, 633615943127, 633615890985, 74296389125, 134454121935, 74296387165,
    118434587065, 118434537031, 535, 10545, 44289, 191919,
    6327, 6327, 14763, 191919, 191919, 6327,
    2368407, 94905, 44289, 191919
  ]
def negativeCoefficients : Array ℕ := #[
    19338713878366007058738708480, 976538743759209246377377792, 29643268045960031451786248192, 17769581902177548115107643392, 12605152785643527865637011456, 1503520265968043662253035094016,
    1081346366713422839612964864, 55005352670295087052578143338496, 26757570733781080052550598656, 851272671668013724801695744, 55003785898918997060206584659968, 874280041172554636282822656,
    874280041172554636282822656, 14793738591419806082364604416, 805257932658931901839441920, 26757570733781080052550598656, 14793738591419806082364604416, 1505088441724621103462038372352,
    851272671668013724801695744, 805257932658931901839441920, 1081346366713422839612964864, 14077309014099813154542321664000, 48162656707357142825041601232896, 14077309012122552774141579100160,
    29311991403914009318006980608, 2342917127879082819161423872, 995935589360236824336281894912, 57974736589859006780526297088, 1844424121947363070403674112, 995935345932390341646611382272,
    1894273422540535045279449088, 1894273422540535045279449088, 32053100281409579845123309568, 1744725520761019120652124160, 57974736589859006780526297088, 32053100281409579845123309568,
    29312234831760492007677493248, 1844424121947363070403674112, 1744725520761019120652124160, 2342917127879082819161423872, 3358166721672870035987669975040, 12193200688092143944891986083840,
    3358166690319169718204466462720, 1461018892985734444080015867904, 1461018772754468257659585822720, 85657904736850783068225536000, 310030097123785335093980037120, 85657902477124634038805463040,
    273091564632940833548407930880, 273091449262391710550444736512, 20696810031802451470969733120, 49797354561860408778424320, 836595556639254867477528576, 1812623706051718879534645248,
    59756825474232490534109184, 956109207587719848545746944, 69716296386604572289794048, 1812623706051718879534645248, 1812623706051718879534645248, 956109207587719848545746944,
    22368971669187695623268204544, 1792704764226974716023275520, 836595556639254867477528576, 1812623706051718879534645248
  ]
def negativeScales : Array ℕ := #[
    27, 28, 32, 32, 44, 50,
    14, 54, 19, 14, 55, 13,
    13, 18, 14, 19, 18, 49,
    14, 14, 14, 51, 52, 51,
    29, 16, 34, 21, 16, 37,
    15, 15, 20, 16, 21, 20,
    32, 16, 16, 16, 41, 43,
    40, 39, 39, 36, 36, 36,
    36, 36, 9, 13, 15, 17,
    12, 12, 13, 17, 17, 12,
    21, 16, 15, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27965478521888712, 28657807750656908, 32581691164337984, 32843396395183412, 44348000261893403, 50246187160767937,
    14804887270297456, 54439342958239089, 19433933799379577, 14459751783535349, 55439301863956849, 13498225931350174,
    13498225931350174, 18578973345237406, 14379581434851302, 19433933799379577, 18578973345237406, 49247691111472031,
    14459751783535349, 14379581434851302, 14804887270297456, 51473142519584919, 52247685916513157, 51473142519382282,
    29565477642308537, 16920364493267946, 34651967192929391, 21549411016800793, 16575229000958025, 37651966840303987,
    15613703148778080, 15613703148778080, 20694450562717709, 16495058652271465, 21549411016800793, 20694450562717709,
    32565489623435436, 16575229000958025, 16495058652271465, 16920364493267946, 41405516703625972, 43265847821422704,
    40405516690156174, 39204817680916007, 39204817562192656, 36112573044993560, 36968323042240558, 36112573006934075,
    36785299504431272, 36785298894948676, 9063395081288510, 13364271474681056, 15434660802572478, 17550138019993724,
    12627305880526679, 12627305880526679, 13849698303573471, 17550138019993724, 17550138019993724, 12627305880526679,
    21175485592194293, 16534196476124184, 15434660802572478, 17550138019993724
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
noncomputable def negativeCeiling : ℝ := 6738844083 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 19338713878366007058738708480, coefficient := (-19338713878366007058738708480) }, { argument := 976538743759209246377377792, coefficient := (-976538743759209246377377792) }, { argument := 29643268045960031451786248192, coefficient := (-29643268045960031451786248192) }, { argument := 17769581902177548115107643392, coefficient := (-17769581902177548115107643392) }, { argument := 12605152785643527865637011456, coefficient := (-12605152785643527865637011456) }, { argument := 1503520265968043662253035094016, coefficient := (-1503520265968043662253035094016) }, { argument := 1081346366713422839612964864, coefficient := (-1081346366713422839612964864) }, { argument := 55005352670295087052578143338496, coefficient := (-55005352670295087052578143338496) }, { argument := 26757570733781080052550598656, coefficient := (-26757570733781080052550598656) }, { argument := 851272671668013724801695744, coefficient := (-851272671668013724801695744) }, { argument := 55003785898918997060206584659968, coefficient := (-55003785898918997060206584659968) }, { argument := 874280041172554636282822656, coefficient := (-874280041172554636282822656) }, { argument := 874280041172554636282822656, coefficient := (-874280041172554636282822656) }, { argument := 14793738591419806082364604416, coefficient := (-14793738591419806082364604416) }, { argument := 805257932658931901839441920, coefficient := (-805257932658931901839441920) }, { argument := 26757570733781080052550598656, coefficient := (-26757570733781080052550598656) }, { argument := 14793738591419806082364604416, coefficient := (-14793738591419806082364604416) }, { argument := 1505088441724621103462038372352, coefficient := (-1505088441724621103462038372352) }, { argument := 851272671668013724801695744, coefficient := (-851272671668013724801695744) }, { argument := 805257932658931901839441920, coefficient := (-805257932658931901839441920) }, { argument := 1081346366713422839612964864, coefficient := (-1081346366713422839612964864) }, { argument := 14077309014099813154542321664000, coefficient := (-14077309014099813154542321664000) }, { argument := 48162656707357142825041601232896, coefficient := (-48162656707357142825041601232896) }, { argument := 14077309012122552774141579100160, coefficient := (-14077309012122552774141579100160) }, { argument := 29311991403914009318006980608, coefficient := (-29311991403914009318006980608) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 995935589360236824336281894912, coefficient := (-995935589360236824336281894912) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 995935345932390341646611382272, coefficient := (-995935345932390341646611382272) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }, { argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }, { argument := 29312234831760492007677493248, coefficient := (-29312234831760492007677493248) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 3358166721672870035987669975040, coefficient := (-3358166721672870035987669975040) }, { argument := 12193200688092143944891986083840, coefficient := (-12193200688092143944891986083840) }, { argument := 3358166690319169718204466462720, coefficient := (-3358166690319169718204466462720) }, { argument := 1461018892985734444080015867904, coefficient := (-1461018892985734444080015867904) }, { argument := 1461018772754468257659585822720, coefficient := (-1461018772754468257659585822720) }, { argument := 85657904736850783068225536000, coefficient := (-85657904736850783068225536000) }, { argument := 310030097123785335093980037120, coefficient := (-310030097123785335093980037120) }, { argument := 85657902477124634038805463040, coefficient := (-85657902477124634038805463040) }, { argument := 273091564632940833548407930880, coefficient := (-273091564632940833548407930880) }, { argument := 273091449262391710550444736512, coefficient := (-273091449262391710550444736512) }, { argument := 20696810031802451470969733120, coefficient := (-20696810031802451470969733120) }, { argument := 49797354561860408778424320, coefficient := (-49797354561860408778424320) }, { argument := 836595556639254867477528576, coefficient := (-836595556639254867477528576) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }, { argument := 59756825474232490534109184, coefficient := (-59756825474232490534109184) }, { argument := 956109207587719848545746944, coefficient := (-956109207587719848545746944) }, { argument := 69716296386604572289794048, coefficient := (-69716296386604572289794048) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }, { argument := 956109207587719848545746944, coefficient := (-956109207587719848545746944) }, { argument := 22368971669187695623268204544, coefficient := (-22368971669187695623268204544) }, { argument := 1792704764226974716023275520, coefficient := (-1792704764226974716023275520) }, { argument := 836595556639254867477528576, coefficient := (-836595556639254867477528576) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }] }

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
def constantNumerator : ℤ := (-142168192457526466002178413690880)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14763, 94905, 14763, 191919, 191919, 6327,
    26339139, 9541, 882474941, 236089, 7511, 7059797803,
    3857, 3857, 130529, 7105, 236089, 130529,
    210714837, 7511, 7105, 9541, 9975, 41895,
    181545, 5985, 5985, 13965, 181545, 181545,
    5985, 2240385, 89775, 41895, 181545, 13965,
    89775, 13965, 181545, 181545, 5985, 16311285,
    61335, 529876395, 1517715, 48285, 4239010125, 24795,
    24795, 839115, 45675, 1517715, 839115, 130491315,
    48285, 45675, 61335, 74144687085, 268389564317, 37072342587,
    26339139, 9541, 882474941, 236089
  ]
def negativeCoefficients : Array ℕ := #[
    69716296386604572289794048, 1792704764226974716023275520, 69716296386604572289794048, 1812623706051718879534645248, 1812623706051718879534645248, 59756825474232490534109184,
    971742712509724251282997248, 90112197226118569967747072, 32557578776177872426932109312, 2229797561148423337712549888, 70939389305667810400141312, 32557570821019490639687974912,
    72856670097712886356901888, 72856670097712886356901888, 1232811549284983840197050368, 67104827721577658486620160, 2229797561148423337712549888, 1232811549284983840197050368,
    971750667668106038527131648, 70939389305667810400141312, 67104827721577658486620160, 90112197226118569967747072, 47105605666624711006617600, 791374175199295144911175680,
    1714644046265139480640880640, 56526726799949653207941120, 904427628799194451327057920, 65947847933274595409264640, 1714644046265139480640880640, 1714644046265139480640880640,
    904427628799194451327057920, 21159838065447820184172625920, 1695801803998489596238233600, 791374175199295144911175680, 1714644046265139480640880640, 65947847933274595409264640,
    1695801803998489596238233600, 65947847933274595409264640, 1714644046265139480640880640, 1714644046265139480640880640, 56526726799949653207941120, 19256966394133600232370339840,
    2317170785814477513456353280, 625567631952949215190560276480, 57337651572388028684036997120, 1824155725002886553146490880, 625567479213908284875472896000, 1873457231084045649177477120,
    1873457231084045649177477120, 31700868410185298747924152320, 1725552712840568361084518400, 57337651572388028684036997120, 31700868410185298747924152320, 19257119133174530547457720320,
    1824155725002886553146490880, 1725552712840568361084518400, 2317170785814477513456353280, 85483004192642054983998504960, 309432100313131768263728955392, 85483001989409059680313933824,
    971742712509724251282997248, 90112197226118569967747072, 32557578776177872426932109312, 2229797561148423337712549888
  ]
def negativeScales : Array ℕ := #[
    13, 16, 13, 17, 17, 12,
    24, 13, 29, 17, 12, 32,
    11, 11, 16, 12, 17, 16,
    27, 12, 12, 13, 13, 15,
    17, 12, 12, 13, 17, 17,
    12, 21, 16, 15, 17, 13,
    16, 13, 17, 17, 12, 23,
    15, 28, 20, 15, 31, 14,
    14, 19, 15, 20, 19, 26,
    15, 15, 15, 36, 37, 35,
    24, 13, 29, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13849698303573471, 16534196476124184, 13849698303573471, 17550138019993724, 17550138019993724, 12627305880526679,
    24650704850346544, 13219924768862814, 29716980071008432, 17848971300356817, 12874789285573854, 32716979718498528,
    11913263436158230, 11913263436158230, 16994010866026276, 12794618934708820, 17848971300356817, 16994010866026276,
    27650716660901363, 12874789285573854, 12794618934708820, 13219924768862814, 13284101125997071, 15354490453888470,
    17469967671308501, 12547135531832084, 12547135531832084, 13769527953509885, 17469967671308501, 17469967671308501,
    12547135531832084, 21095315243510310, 16454026127439437, 15354490453888470, 17469967671308501, 13769527953509885,
    16454026127439437, 13769527953509885, 17469967671308501, 17469967671308501, 12547135531832084, 23959367118185431,
    15904422947861917, 28981080636006465, 20533469472931265, 15559287457087955, 31981080283756867, 14597761604906147,
    14597761604906147, 19678509018828490, 15479117108402347, 20533469472931265, 19678509018828490, 26959378561058800,
    15559287457087955, 15479117108402347, 15904422947861917, 36109624267437071, 37965537634180512, 35109624230253149,
    24650704850346544, 13219924768862814, 29716980071008432, 17848971300356817
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
noncomputable def negativeCeiling : ℝ := 780819839 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 69716296386604572289794048, coefficient := (-69716296386604572289794048) }, { argument := 1792704764226974716023275520, coefficient := (-1792704764226974716023275520) }, { argument := 69716296386604572289794048, coefficient := (-69716296386604572289794048) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }, { argument := 59756825474232490534109184, coefficient := (-59756825474232490534109184) }, { argument := 971742712509724251282997248, coefficient := (-971742712509724251282997248) }, { argument := 90112197226118569967747072, coefficient := (-90112197226118569967747072) }, { argument := 32557578776177872426932109312, coefficient := (-32557578776177872426932109312) }, { argument := 2229797561148423337712549888, coefficient := (-2229797561148423337712549888) }, { argument := 70939389305667810400141312, coefficient := (-70939389305667810400141312) }, { argument := 32557570821019490639687974912, coefficient := (-32557570821019490639687974912) }, { argument := 72856670097712886356901888, coefficient := (-72856670097712886356901888) }, { argument := 72856670097712886356901888, coefficient := (-72856670097712886356901888) }, { argument := 1232811549284983840197050368, coefficient := (-1232811549284983840197050368) }, { argument := 67104827721577658486620160, coefficient := (-67104827721577658486620160) }, { argument := 2229797561148423337712549888, coefficient := (-2229797561148423337712549888) }, { argument := 1232811549284983840197050368, coefficient := (-1232811549284983840197050368) }, { argument := 971750667668106038527131648, coefficient := (-971750667668106038527131648) }, { argument := 70939389305667810400141312, coefficient := (-70939389305667810400141312) }, { argument := 67104827721577658486620160, coefficient := (-67104827721577658486620160) }, { argument := 90112197226118569967747072, coefficient := (-90112197226118569967747072) }, { argument := 47105605666624711006617600, coefficient := (-47105605666624711006617600) }, { argument := 791374175199295144911175680, coefficient := (-791374175199295144911175680) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }, { argument := 56526726799949653207941120, coefficient := (-56526726799949653207941120) }, { argument := 904427628799194451327057920, coefficient := (-904427628799194451327057920) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }, { argument := 904427628799194451327057920, coefficient := (-904427628799194451327057920) }, { argument := 21159838065447820184172625920, coefficient := (-21159838065447820184172625920) }, { argument := 1695801803998489596238233600, coefficient := (-1695801803998489596238233600) }, { argument := 791374175199295144911175680, coefficient := (-791374175199295144911175680) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 1695801803998489596238233600, coefficient := (-1695801803998489596238233600) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }, { argument := 56526726799949653207941120, coefficient := (-56526726799949653207941120) }, { argument := 19256966394133600232370339840, coefficient := (-19256966394133600232370339840) }, { argument := 2317170785814477513456353280, coefficient := (-2317170785814477513456353280) }, { argument := 625567631952949215190560276480, coefficient := (-625567631952949215190560276480) }, { argument := 57337651572388028684036997120, coefficient := (-57337651572388028684036997120) }, { argument := 1824155725002886553146490880, coefficient := (-1824155725002886553146490880) }, { argument := 625567479213908284875472896000, coefficient := (-625567479213908284875472896000) }, { argument := 1873457231084045649177477120, coefficient := (-1873457231084045649177477120) }, { argument := 1873457231084045649177477120, coefficient := (-1873457231084045649177477120) }, { argument := 31700868410185298747924152320, coefficient := (-31700868410185298747924152320) }, { argument := 1725552712840568361084518400, coefficient := (-1725552712840568361084518400) }, { argument := 57337651572388028684036997120, coefficient := (-57337651572388028684036997120) }, { argument := 31700868410185298747924152320, coefficient := (-31700868410185298747924152320) }, { argument := 19257119133174530547457720320, coefficient := (-19257119133174530547457720320) }, { argument := 1824155725002886553146490880, coefficient := (-1824155725002886553146490880) }, { argument := 1725552712840568361084518400, coefficient := (-1725552712840568361084518400) }, { argument := 2317170785814477513456353280, coefficient := (-2317170785814477513456353280) }, { argument := 85483004192642054983998504960, coefficient := (-85483004192642054983998504960) }, { argument := 309432100313131768263728955392, coefficient := (-309432100313131768263728955392) }, { argument := 85483001989409059680313933824, coefficient := (-85483001989409059680313933824) }, { argument := 971742712509724251282997248, coefficient := (-971742712509724251282997248) }, { argument := 90112197226118569967747072, coefficient := (-90112197226118569967747072) }, { argument := 32557578776177872426932109312, coefficient := (-32557578776177872426932109312) }, { argument := 2229797561148423337712549888, coefficient := (-2229797561148423337712549888) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
