import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

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
def constantNumerator : ℤ := (-472627040987882263685929071804416)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10122210025, 491589575, 11998715, 52612865123, 525863146471, 1051726035919,
    52612865123, 697965273, 5085040881, 1395931485, 1673840077, 16729953929,
    33459899681, 1673840077, 1420459677, 10348789269, 2840921265, 14361027,
    1283661051, 91909741, 12152620195, 3580899, 5968165, 182625849,
    5968165, 3580899, 2925594483, 187400381, 1283661051, 182625849,
    5968165, 187400381, 5968165, 182625849, 5968165, 14361027,
    2194067083, 19147765, 21267975469, 216096205, 19147765, 42535940551,
    19147765, 19147765, 793811629, 4923711, 216096205, 793811629,
    2194067083, 19147765, 4923711, 19147765, 69127551, 503630247,
    138255195, 135716763, 1356482751, 2712964839, 135716763, 211842495,
    1543383015, 423685275, 69127551, 503630247
  ]
def negativeCoefficients : Array ℕ := #[
    1493774542332097298445841203200, 145091633269258354437600051200, 885348899273519610472693760, 60658503619286263090588418048, 2425115720186544290439085686784, 2425115127531856533307825061888,
    60658503619286263090588418048, 12875186763367819316369031168, 46901223868078773643769806848, 12875195424114161923003514880, 1929806220046080597035057152, 77153294623303644665731874816,
    77153275768425358325356429312, 1929806220046080597035057152, 13101428064321566940139094016, 47725366779498688196615602176, 13101436877253548154877378560, 66228547426158215228817408,
    5919841721296506124033327104, 847717735053964899126345728, 56044068640539816383249121280, 528447419254419677377462272, 27523303086167691530076160, 842213074436731360820330496,
    880745698757366128962437120, 528447419254419677377462272, 13491923172839402388043333632, 864231716905665514044391424, 5919841721296506124033327104, 842213074436731360820330496,
    27523303086167691530076160, 864231716905665514044391424, 27523303086167691530076160, 842213074436731360820330496, 880745698757366128962437120, 66228547426158215228817408,
    2529587122540715806459691008, 88303480134633293149634560, 98081225110643967900019326976, 996567847233718594117304320, 88303480134633293149634560, 98081201159852631197380247552,
    88303480134633293149634560, 88303480134633293149634560, 3660809990724368810289135616, 90826436709908530096766976, 996567847233718594117304320, 3660809990724368810289135616,
    2529587122540715806459691008, 88303480134633293149634560, 90826436709908530096766976, 88303480134633293149634560, 637589120869652394261086208, 2322584568547031921656332288,
    637589549756452108008161280, 2503532393573293747504939008, 100090760592393917404192702464, 100090736132011275665327259648, 2503532393573293747504939008, 15631217156804381278658887680,
    56940782970830460014800404480, 15631227671448503293103308800, 637589120869652394261086208, 2322584568547031921656332288
  ]
def negativeScales : Array ℕ := #[
    33, 28, 23, 35, 38, 39,
    35, 29, 32, 30, 30, 33,
    34, 30, 30, 33, 31, 23,
    30, 26, 33, 21, 22, 27,
    22, 21, 31, 27, 30, 27,
    22, 27, 22, 27, 22, 23,
    31, 24, 34, 27, 24, 35,
    24, 24, 29, 22, 27, 29,
    31, 24, 22, 24, 26, 28,
    27, 27, 30, 31, 27, 27,
    30, 28, 26, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33236805263017984, 28872879082975162, 23516376573179666, 35614696565504733, 38935896445400177, 39935896092831351,
    35614696565504733, 29378580016569604, 32243612226609625, 30378580987026330, 30640514549668721, 33961714434044193,
    34961714081475342, 30640514549668721, 30403710731893291, 33268742941933307, 31403711702350017, 23775655588889764,
    30257617165016852, 26453714437016999, 33500548351988085, 21771890397403388, 22508855991209770, 27444315739014734,
    22508855991209770, 21771890397403388, 31446082665188924, 27481548645213816, 30257617165016852, 27444315739014734,
    22508855991209770, 27481548645213816, 22508855991209770, 27444315739014734, 22508855991209770, 23775655588889764,
    31030960490407357, 24190672669333438, 34307963656368439, 27687098495506215, 24190672669333438, 35307963304071737,
    24190672669333438, 24190672669333438, 29564221456457250, 22231314653830784, 27687098495506215, 29564221456457250,
    31030960490407357, 24190672669333438, 22231314653830784, 24190672669333438, 26042757480023858, 28907789695082770,
    27042758450480585, 27016023684744221, 30337223556449404, 31337223203880627, 27016023684744221, 27658416777994287,
    30523448988008537, 28658417748451014, 26042757480023858, 28907789695082770
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
noncomputable def negativeCeiling : ℝ := 839040809 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1493774542332097298445841203200, coefficient := (-1493774542332097298445841203200) }, { argument := 145091633269258354437600051200, coefficient := (-145091633269258354437600051200) }, { argument := 885348899273519610472693760, coefficient := (-885348899273519610472693760) }, { argument := 60658503619286263090588418048, coefficient := (-60658503619286263090588418048) }, { argument := 2425115720186544290439085686784, coefficient := (-2425115720186544290439085686784) }, { argument := 2425115127531856533307825061888, coefficient := (-2425115127531856533307825061888) }, { argument := 60658503619286263090588418048, coefficient := (-60658503619286263090588418048) }, { argument := 12875186763367819316369031168, coefficient := (-12875186763367819316369031168) }, { argument := 46901223868078773643769806848, coefficient := (-46901223868078773643769806848) }, { argument := 12875195424114161923003514880, coefficient := (-12875195424114161923003514880) }, { argument := 1929806220046080597035057152, coefficient := (-1929806220046080597035057152) }, { argument := 77153294623303644665731874816, coefficient := (-77153294623303644665731874816) }, { argument := 77153275768425358325356429312, coefficient := (-77153275768425358325356429312) }, { argument := 1929806220046080597035057152, coefficient := (-1929806220046080597035057152) }, { argument := 13101428064321566940139094016, coefficient := (-13101428064321566940139094016) }, { argument := 47725366779498688196615602176, coefficient := (-47725366779498688196615602176) }, { argument := 13101436877253548154877378560, coefficient := (-13101436877253548154877378560) }, { argument := 66228547426158215228817408, coefficient := (-66228547426158215228817408) }, { argument := 5919841721296506124033327104, coefficient := (-5919841721296506124033327104) }, { argument := 847717735053964899126345728, coefficient := (-847717735053964899126345728) }, { argument := 56044068640539816383249121280, coefficient := (-56044068640539816383249121280) }, { argument := 528447419254419677377462272, coefficient := (-528447419254419677377462272) }, { argument := 27523303086167691530076160, coefficient := (-27523303086167691530076160) }, { argument := 842213074436731360820330496, coefficient := (-842213074436731360820330496) }, { argument := 880745698757366128962437120, coefficient := (-880745698757366128962437120) }, { argument := 528447419254419677377462272, coefficient := (-528447419254419677377462272) }, { argument := 13491923172839402388043333632, coefficient := (-13491923172839402388043333632) }, { argument := 864231716905665514044391424, coefficient := (-864231716905665514044391424) }, { argument := 5919841721296506124033327104, coefficient := (-5919841721296506124033327104) }, { argument := 842213074436731360820330496, coefficient := (-842213074436731360820330496) }, { argument := 27523303086167691530076160, coefficient := (-27523303086167691530076160) }, { argument := 864231716905665514044391424, coefficient := (-864231716905665514044391424) }, { argument := 27523303086167691530076160, coefficient := (-27523303086167691530076160) }, { argument := 842213074436731360820330496, coefficient := (-842213074436731360820330496) }, { argument := 880745698757366128962437120, coefficient := (-880745698757366128962437120) }, { argument := 66228547426158215228817408, coefficient := (-66228547426158215228817408) }, { argument := 2529587122540715806459691008, coefficient := (-2529587122540715806459691008) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 98081225110643967900019326976, coefficient := (-98081225110643967900019326976) }, { argument := 996567847233718594117304320, coefficient := (-996567847233718594117304320) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 98081201159852631197380247552, coefficient := (-98081201159852631197380247552) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 3660809990724368810289135616, coefficient := (-3660809990724368810289135616) }, { argument := 90826436709908530096766976, coefficient := (-90826436709908530096766976) }, { argument := 996567847233718594117304320, coefficient := (-996567847233718594117304320) }, { argument := 3660809990724368810289135616, coefficient := (-3660809990724368810289135616) }, { argument := 2529587122540715806459691008, coefficient := (-2529587122540715806459691008) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 90826436709908530096766976, coefficient := (-90826436709908530096766976) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 637589120869652394261086208, coefficient := (-637589120869652394261086208) }, { argument := 2322584568547031921656332288, coefficient := (-2322584568547031921656332288) }, { argument := 637589549756452108008161280, coefficient := (-637589549756452108008161280) }, { argument := 2503532393573293747504939008, coefficient := (-2503532393573293747504939008) }, { argument := 100090760592393917404192702464, coefficient := (-100090760592393917404192702464) }, { argument := 100090736132011275665327259648, coefficient := (-100090736132011275665327259648) }, { argument := 2503532393573293747504939008, coefficient := (-2503532393573293747504939008) }, { argument := 15631217156804381278658887680, coefficient := (-15631217156804381278658887680) }, { argument := 56940782970830460014800404480, coefficient := (-56940782970830460014800404480) }, { argument := 15631227671448503293103308800, coefficient := (-15631227671448503293103308800) }, { argument := 637589120869652394261086208, coefficient := (-637589120869652394261086208) }, { argument := 2322584568547031921656332288, coefficient := (-2322584568547031921656332288) }] }

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
def constantNumerator : ℤ := 11659003978983443571346214844628992
def positiveArguments : Array ℕ := #[
    855, 403, 455, 195, 5135, 455,
    195, 455, 455, 18863, 117, 5135,
    18863, 403, 455, 117, 455, 3453,
    100137, 88627, 5755, 3453, 5755, 176103,
    5755, 3453, 2821101, 180707, 100137, 176103,
    5755, 180707, 5755, 176103, 5755, 3453,
    20821, 15505, 16391, 1329, 284849, 515209,
    15505, 284849, 8417, 8417, 16391, 16391,
    515209, 16391, 20821, 1329, 93, 285,
    843, 1881, 93, 939, 1911, 93
  ]
def positiveCoefficients : Array ℕ := #[
    135480157899392017284960155074560, 62361229479001031348043382784, 70407839734356003134887690240, 60349576915162288401332305920, 794602762716303463950875361280, 70407839734356003134887690240,
    60349576915162288401332305920, 70407839734356003134887690240, 70407839734356003134887690240, 2918907870130016015677772529664, 72419492298194746081598767104, 794602762716303463950875361280,
    2918907870130016015677772529664, 62361229479001031348043382784, 70407839734356003134887690240, 72419492298194746081598767104, 70407839734356003134887690240, 133581467364138065288333623296,
    1936931276780001946680837537792, 3428590995679543675733896331264, 111317889470115054406944686080, 2137303477826209044613337972736, 111317889470115054406944686080, 3406327417785520664852507394048,
    3562172463043681741022229954560, 2137303477826209044613337972736, 54568029418250399670284285116416, 3495381729361612708378063142912, 1936931276780001946680837537792, 3406327417785520664852507394048,
    111317889470115054406944686080, 3495381729361612708378063142912, 111317889470115054406944686080, 3406327417785520664852507394048, 3562172463043681741022229954560, 133581467364138065288333623296,
    402736711843139104744916647936, 299910317329997205661108142080, 317048049748854188841742893056, 411305578052567596335234023424, 5509780972662520092574072438784, 9965591401565335719539107692544,
    299910317329997205661108142080, 5509780972662520092574072438784, 325616915958282680432060268544, 325616915958282680432060268544, 317048049748854188841742893056, 317048049748854188841742893056,
    9965591401565335719539107692544, 317048049748854188841742893056, 402736711843139104744916647936, 411305578052567596335234023424, 7195526478346272847851159552, 176406455598166689173125201920,
    130447931639696946467495215104, 145535325868487518567828291584, 7195526478346272847851159552, 145303212111121509766284705792, 147856463442147606583264149504, 7195526478346272847851159552
  ]
def positiveScales : Array ℕ := #[
    9, 8, 8, 7, 12, 8,
    7, 8, 8, 14, 6, 12,
    14, 8, 8, 6, 8, 11,
    16, 16, 12, 11, 12, 17,
    12, 11, 21, 17, 16, 17,
    12, 17, 12, 17, 12, 11,
    14, 13, 14, 10, 18, 18,
    13, 18, 13, 13, 14, 14,
    18, 14, 14, 10, 6, 8,
    9, 10, 6, 9, 10, 6
  ]
def negativeArguments : Array ℕ := #[
    138255195, 13, 1151, 443
  ]
def negativeCoefficients : Array ℕ := #[
    637589549756452108008161280, 8239728901483491109728570834944, 91191615053918252570169086836736, 35098075993819101553939969998848
  ]
def negativeScales : Array ℕ := #[
    27, 3, 10, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9739780609762119, 8654636028526477, 8829722735013603, 7607330313749179, 12326148561205557, 8829722735013603,
    7607330313749179, 8829722735013603, 8829722735013603, 14203271522207836, 6870364719426147, 12326148561205557,
    14203271522207836, 8654636028526477, 8829722735013603, 6870364719426147, 8829722735013603, 11753634618838289,
    16611615613980474, 16435458658827129, 12490600213019580, 11753634618838289, 12490600213019580, 17426059960824880,
    12490600213019580, 11753634618838289, 21427826886999068, 17463292867023852, 16611615613980474, 17426059960824880,
    12490600213019580, 17463292867023852, 12490600213019580, 17426059960824880, 12490600213019580, 11753634618838289,
    14345751740232655, 13920445905112445, 14000616254183968, 10376125389276173, 18119837815882965, 18974798269056584,
    13920445905112445, 18119837815882965, 13039090401998603, 13039090401998603, 14000616254183968, 14000616254183968,
    18974798269056584, 14000616254183968, 14345751740232655, 10376125389276173, 6539158811107971, 8154818109052103,
    9719388820935039, 10877284133344468, 6539158811107971, 9874981347482478, 10900112062706946, 6539158811107971
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    27042758450480585, 3700439718214233, 10168672118132231, 8791162889093957
  ]

abbrev PositiveTerm := Fin 60
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 4582350233 / 100000000000
noncomputable def negativeCeiling : ℝ := 3048646951 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 637589549756452108008161280, coefficient := (-637589549756452108008161280) }, { argument := 135480157899392017284960155074560, coefficient := 135480157899392017284960155074560 }, { argument := 62361229479001031348043382784, coefficient := 62361229479001031348043382784 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 60349576915162288401332305920, coefficient := 60349576915162288401332305920 }, { argument := 794602762716303463950875361280, coefficient := 794602762716303463950875361280 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 60349576915162288401332305920, coefficient := 60349576915162288401332305920 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 2918907870130016015677772529664, coefficient := 2918907870130016015677772529664 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 794602762716303463950875361280, coefficient := 794602762716303463950875361280 }, { argument := 2918907870130016015677772529664, coefficient := 2918907870130016015677772529664 }, { argument := 62361229479001031348043382784, coefficient := 62361229479001031348043382784 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 8239728901483491109728570834944, coefficient := (-8239728901483491109728570834944) }, { argument := 133581467364138065288333623296, coefficient := 133581467364138065288333623296 }, { argument := 1936931276780001946680837537792, coefficient := 1936931276780001946680837537792 }, { argument := 3428590995679543675733896331264, coefficient := 3428590995679543675733896331264 }, { argument := 111317889470115054406944686080, coefficient := 111317889470115054406944686080 }, { argument := 2137303477826209044613337972736, coefficient := 2137303477826209044613337972736 }, { argument := 111317889470115054406944686080, coefficient := 111317889470115054406944686080 }, { argument := 3406327417785520664852507394048, coefficient := 3406327417785520664852507394048 }, { argument := 3562172463043681741022229954560, coefficient := 3562172463043681741022229954560 }, { argument := 2137303477826209044613337972736, coefficient := 2137303477826209044613337972736 }, { argument := 54568029418250399670284285116416, coefficient := 54568029418250399670284285116416 }, { argument := 3495381729361612708378063142912, coefficient := 3495381729361612708378063142912 }, { argument := 1936931276780001946680837537792, coefficient := 1936931276780001946680837537792 }, { argument := 3406327417785520664852507394048, coefficient := 3406327417785520664852507394048 }, { argument := 111317889470115054406944686080, coefficient := 111317889470115054406944686080 }, { argument := 3495381729361612708378063142912, coefficient := 3495381729361612708378063142912 }, { argument := 111317889470115054406944686080, coefficient := 111317889470115054406944686080 }, { argument := 3406327417785520664852507394048, coefficient := 3406327417785520664852507394048 }, { argument := 3562172463043681741022229954560, coefficient := 3562172463043681741022229954560 }, { argument := 133581467364138065288333623296, coefficient := 133581467364138065288333623296 }, { argument := 91191615053918252570169086836736, coefficient := (-91191615053918252570169086836736) }, { argument := 402736711843139104744916647936, coefficient := 402736711843139104744916647936 }, { argument := 299910317329997205661108142080, coefficient := 299910317329997205661108142080 }, { argument := 317048049748854188841742893056, coefficient := 317048049748854188841742893056 }, { argument := 411305578052567596335234023424, coefficient := 411305578052567596335234023424 }, { argument := 5509780972662520092574072438784, coefficient := 5509780972662520092574072438784 }, { argument := 9965591401565335719539107692544, coefficient := 9965591401565335719539107692544 }, { argument := 299910317329997205661108142080, coefficient := 299910317329997205661108142080 }, { argument := 5509780972662520092574072438784, coefficient := 5509780972662520092574072438784 }, { argument := 325616915958282680432060268544, coefficient := 325616915958282680432060268544 }, { argument := 325616915958282680432060268544, coefficient := 325616915958282680432060268544 }, { argument := 317048049748854188841742893056, coefficient := 317048049748854188841742893056 }, { argument := 317048049748854188841742893056, coefficient := 317048049748854188841742893056 }, { argument := 9965591401565335719539107692544, coefficient := 9965591401565335719539107692544 }, { argument := 317048049748854188841742893056, coefficient := 317048049748854188841742893056 }, { argument := 402736711843139104744916647936, coefficient := 402736711843139104744916647936 }, { argument := 411305578052567596335234023424, coefficient := 411305578052567596335234023424 }, { argument := 35098075993819101553939969998848, coefficient := (-35098075993819101553939969998848) }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 147856463442147606583264149504, coefficient := 147856463442147606583264149504 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }] }

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

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3078783920117176038485434495401984)
def positiveArguments : Array ℕ := #[
    285, 93, 2229921, 16246137, 4459845, 90682543,
    906367811, 1812735179, 90682543, 4787009, 196124645, 4038358315,
    196124645, 4787009, 547079, 108504825, 108504825, 547079
  ]
def positiveCoefficients : Array ℕ := #[
    176406455598166689173125201920, 7195526478346272847851159552, 168488067037554593993123168256, 613761702759267274264795938816, 168488180374350182864608296960, 428236201644585365485731708928,
    17120803887273317322737082957824, 17120799703256613500231423623168, 428236201644585365485731708928, 45212021709590674929539350528, 7409379600101661990496617103360, 76282431810295747239316773928960,
    7409379600101661990496617103360, 45212021709590674929539350528, 20668060264654741070908751872, 4099196390477090813793376665600, 4099196390477090813793376665600, 20668060264654741070908751872
  ]
def positiveScales : Array ℕ := #[
    8, 6, 21, 23, 22, 26,
    29, 30, 26, 22, 27, 31,
    27, 22, 19, 26, 26, 19
  ]
def negativeArguments : Array ℕ := #[
    3, 3, 443, 1151, 13
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 950737950171172051122527404032, 35098075993819101553939969998848, 91191615053918252570169086836736, 8239728901483491109728570834944
  ]
def negativeScales : Array ℕ := #[
    1, 1, 8, 10, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8154818109052103, 6539158811107971, 21088561169636982, 23953593378993411, 22088562140093708, 26434321513186649,
    29755521384876105, 30755521032307328, 26434321513186649, 22190693087778586, 27547195594910662, 31911121777288366,
    27547195594910662, 22190693087778586, 19061389652388470, 26693183957053295, 26693183957053295, 19061389652388470
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 1584962500724866, 8791162889093957, 10168672118132231, 3700439718214233
  ]

abbrev PositiveTerm := Fin 18
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
noncomputable def positiveFloor : ℝ := 24954087753 / 500000000000
noncomputable def negativeCeiling : ℝ := 7639652061 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 168488067037554593993123168256, coefficient := 168488067037554593993123168256 }, { argument := 613761702759267274264795938816, coefficient := 613761702759267274264795938816 }, { argument := 168488180374350182864608296960, coefficient := 168488180374350182864608296960 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 428236201644585365485731708928, coefficient := 428236201644585365485731708928 }, { argument := 17120803887273317322737082957824, coefficient := 17120803887273317322737082957824 }, { argument := 17120799703256613500231423623168, coefficient := 17120799703256613500231423623168 }, { argument := 428236201644585365485731708928, coefficient := 428236201644585365485731708928 }, { argument := 35098075993819101553939969998848, coefficient := (-35098075993819101553939969998848) }, { argument := 45212021709590674929539350528, coefficient := 45212021709590674929539350528 }, { argument := 7409379600101661990496617103360, coefficient := 7409379600101661990496617103360 }, { argument := 76282431810295747239316773928960, coefficient := 76282431810295747239316773928960 }, { argument := 7409379600101661990496617103360, coefficient := 7409379600101661990496617103360 }, { argument := 45212021709590674929539350528, coefficient := 45212021709590674929539350528 }, { argument := 91191615053918252570169086836736, coefficient := (-91191615053918252570169086836736) }, { argument := 20668060264654741070908751872, coefficient := 20668060264654741070908751872 }, { argument := 4099196390477090813793376665600, coefficient := 4099196390477090813793376665600 }, { argument := 4099196390477090813793376665600, coefficient := 4099196390477090813793376665600 }, { argument := 20668060264654741070908751872, coefficient := 20668060264654741070908751872 }, { argument := 8239728901483491109728570834944, coefficient := (-8239728901483491109728570834944) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
