import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4135198545023190816684474336542720)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3249, 3249, 7581, 98553, 98553, 3249,
    1216209, 48735, 22743, 98553, 7581, 48735,
    7581, 98553, 98553, 3249, 782932587, 4089,
    27675706773, 101181, 3219, 221405600019, 1653, 1653,
    55941, 3045, 101181, 55941, 6263514861, 3219,
    3045, 4089, 6251579899351193, 10694256118669927, 6251579898473113, 26339139,
    9541, 882474941, 236089, 7511, 7059797803, 3857,
    3857, 130529, 7105, 236089, 130529, 210714837,
    7511, 7105, 9541, 74296389125, 134454121935, 74296387165,
    56824836871, 56824835321, 5415, 22743, 98553, 3249,
    3249, 7581, 98553, 98553
  ]
def negativeCoefficients : Array ℕ := #[
    61371874811373909197193216, 981949996981982547155091456, 71600520613269560730058752, 1861613535945008578981527552, 1861613535945008578981527552, 981949996981982547155091456,
    22973538471057633342815993856, 1841156244341217275915796480, 859206247359234728760705024, 1861613535945008578981527552, 71600520613269560730058752, 1841156244341217275915796480,
    71600520613269560730058752, 1861613535945008578981527552, 1861613535945008578981527552, 61371874811373909197193216, 28885114118712675866649821184, 1235824419101054673843388416,
    1021053359801122097787448590336, 30580080838606948631486398464, 972883053334872828344795136, 1021053110009148909667982770176, 999177189911491012894654464, 999177189911491012894654464,
    16907129818765492665559547904, 920294780181636459245076480, 30580080838606948631486398464, 16907129818765492665559547904, 28885363910685863986115641344, 972883053334872828344795136,
    920294780181636459245076480, 1235824419101054673843388416, 14077306452597457841597515300864, 48162647871046530088259962273792, 14077306450620197461196772737024, 971742712509724251282997248,
    90112197226118569967747072, 32557578776177872426932109312, 2229797561148423337712549888, 70939389305667810400141312, 32557570821019490639687974912, 72856670097712886356901888,
    72856670097712886356901888, 1232811549284983840197050368, 67104827721577658486620160, 2229797561148423337712549888, 1232811549284983840197050368, 971750667668106038527131648,
    70939389305667810400141312, 67104827721577658486620160, 90112197226118569967747072, 85657904736850783068225536000, 310030097123785335093980037120, 85657902477124634038805463040,
    131029152848703908801719304192, 131029149274647244520493678592, 51143229009478257664327680, 859206247359234728760705024, 1861613535945008578981527552, 61371874811373909197193216,
    981949996981982547155091456, 71600520613269560730058752, 1861613535945008578981527552, 1861613535945008578981527552
  ]
def negativeScales : Array ℕ := #[
    11, 11, 12, 16, 16, 11,
    20, 15, 14, 16, 12, 15,
    12, 16, 16, 11, 29, 11,
    34, 16, 11, 37, 10, 10,
    15, 11, 16, 15, 32, 11,
    11, 11, 52, 53, 52, 24,
    13, 29, 17, 12, 32, 11,
    11, 16, 12, 17, 16, 27,
    12, 12, 13, 36, 36, 36,
    35, 35, 12, 14, 16, 11,
    11, 12, 16, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11665780028361156, 11665780028361156, 12888172453193550, 16588612167811137, 16588612167811137, 11665780028361156,
    20213959740008929, 15572670623940608, 14473134950387196, 16588612167811137, 12888172453193550, 15572670623940608,
    12888172453193550, 16588612167811137, 16588612167811137, 11665780028361156, 29544312851306353, 11997532370288072,
    34687901109471610, 16626578877333553, 11652396861500322, 37687900756528561, 10690871009350625, 10690871009350625,
    15771618423534793, 11572226512796267, 16626578877333553, 15771618423534793, 32544325327354787, 11652396861500322,
    11572226512796267, 11997532370288072, 52473142257072597, 53247685651824629, 52473142256869960, 24650704850346544,
    13219924768862814, 29716980071008432, 17848971300356817, 12874789285573854, 32716979718498528, 11913263436158230,
    11913263436158230, 16994010866026276, 12794618934708820, 17848971300356817, 16994010866026276, 27650716660901363,
    12874789285573854, 12794618934708820, 13219924768862814, 36112573044993560, 36968323042240558, 36112573006934075,
    35725802586460054, 35725802547107942, 12402745622495697, 14473134950387196, 16588612167811137, 11665780028361156,
    11665780028361156, 12888172453193550, 16588612167811137, 16588612167811137
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
noncomputable def negativeCeiling : ℝ := 12486363797 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 61371874811373909197193216, coefficient := (-61371874811373909197193216) }, { argument := 981949996981982547155091456, coefficient := (-981949996981982547155091456) }, { argument := 71600520613269560730058752, coefficient := (-71600520613269560730058752) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }, { argument := 981949996981982547155091456, coefficient := (-981949996981982547155091456) }, { argument := 22973538471057633342815993856, coefficient := (-22973538471057633342815993856) }, { argument := 1841156244341217275915796480, coefficient := (-1841156244341217275915796480) }, { argument := 859206247359234728760705024, coefficient := (-859206247359234728760705024) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }, { argument := 71600520613269560730058752, coefficient := (-71600520613269560730058752) }, { argument := 1841156244341217275915796480, coefficient := (-1841156244341217275915796480) }, { argument := 71600520613269560730058752, coefficient := (-71600520613269560730058752) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }, { argument := 61371874811373909197193216, coefficient := (-61371874811373909197193216) }, { argument := 28885114118712675866649821184, coefficient := (-28885114118712675866649821184) }, { argument := 1235824419101054673843388416, coefficient := (-1235824419101054673843388416) }, { argument := 1021053359801122097787448590336, coefficient := (-1021053359801122097787448590336) }, { argument := 30580080838606948631486398464, coefficient := (-30580080838606948631486398464) }, { argument := 972883053334872828344795136, coefficient := (-972883053334872828344795136) }, { argument := 1021053110009148909667982770176, coefficient := (-1021053110009148909667982770176) }, { argument := 999177189911491012894654464, coefficient := (-999177189911491012894654464) }, { argument := 999177189911491012894654464, coefficient := (-999177189911491012894654464) }, { argument := 16907129818765492665559547904, coefficient := (-16907129818765492665559547904) }, { argument := 920294780181636459245076480, coefficient := (-920294780181636459245076480) }, { argument := 30580080838606948631486398464, coefficient := (-30580080838606948631486398464) }, { argument := 16907129818765492665559547904, coefficient := (-16907129818765492665559547904) }, { argument := 28885363910685863986115641344, coefficient := (-28885363910685863986115641344) }, { argument := 972883053334872828344795136, coefficient := (-972883053334872828344795136) }, { argument := 920294780181636459245076480, coefficient := (-920294780181636459245076480) }, { argument := 1235824419101054673843388416, coefficient := (-1235824419101054673843388416) }, { argument := 14077306452597457841597515300864, coefficient := (-14077306452597457841597515300864) }, { argument := 48162647871046530088259962273792, coefficient := (-48162647871046530088259962273792) }, { argument := 14077306450620197461196772737024, coefficient := (-14077306450620197461196772737024) }, { argument := 971742712509724251282997248, coefficient := (-971742712509724251282997248) }, { argument := 90112197226118569967747072, coefficient := (-90112197226118569967747072) }, { argument := 32557578776177872426932109312, coefficient := (-32557578776177872426932109312) }, { argument := 2229797561148423337712549888, coefficient := (-2229797561148423337712549888) }, { argument := 70939389305667810400141312, coefficient := (-70939389305667810400141312) }, { argument := 32557570821019490639687974912, coefficient := (-32557570821019490639687974912) }, { argument := 72856670097712886356901888, coefficient := (-72856670097712886356901888) }, { argument := 72856670097712886356901888, coefficient := (-72856670097712886356901888) }, { argument := 1232811549284983840197050368, coefficient := (-1232811549284983840197050368) }, { argument := 67104827721577658486620160, coefficient := (-67104827721577658486620160) }, { argument := 2229797561148423337712549888, coefficient := (-2229797561148423337712549888) }, { argument := 1232811549284983840197050368, coefficient := (-1232811549284983840197050368) }, { argument := 971750667668106038527131648, coefficient := (-971750667668106038527131648) }, { argument := 70939389305667810400141312, coefficient := (-70939389305667810400141312) }, { argument := 67104827721577658486620160, coefficient := (-67104827721577658486620160) }, { argument := 90112197226118569967747072, coefficient := (-90112197226118569967747072) }, { argument := 85657904736850783068225536000, coefficient := (-85657904736850783068225536000) }, { argument := 310030097123785335093980037120, coefficient := (-310030097123785335093980037120) }, { argument := 85657902477124634038805463040, coefficient := (-85657902477124634038805463040) }, { argument := 131029152848703908801719304192, coefficient := (-131029152848703908801719304192) }, { argument := 131029149274647244520493678592, coefficient := (-131029149274647244520493678592) }, { argument := 51143229009478257664327680, coefficient := (-51143229009478257664327680) }, { argument := 859206247359234728760705024, coefficient := (-859206247359234728760705024) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }, { argument := 61371874811373909197193216, coefficient := (-61371874811373909197193216) }, { argument := 981949996981982547155091456, coefficient := (-981949996981982547155091456) }, { argument := 71600520613269560730058752, coefficient := (-71600520613269560730058752) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }] }

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

end TermShard4


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-202034951998888944284513505116160)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3249, 1216209, 48735, 22743, 98553, 7581,
    48735, 7581, 98553, 98553, 3249, 183255,
    769671, 3335241, 109953, 109953, 256557, 3335241,
    3335241, 109953, 41159073, 1649295, 769671, 3335241,
    256557, 1649295, 256557, 3335241, 3335241, 109953,
    794503119, 124033, 26994888241, 3069157, 97643, 215959053143,
    50141, 50141, 1696877, 92365, 3069157, 1696877,
    6356077737, 97643, 92365, 124033, 9975, 41895,
    181545, 5985, 5985, 13965, 181545, 181545,
    5985, 2240385, 89775, 41895, 181545, 13965,
    89775, 13965, 181545, 181545
  ]
def negativeCoefficients : Array ℕ := #[
    981949996981982547155091456, 22973538471057633342815993856, 1841156244341217275915796480, 859206247359234728760705024, 1861613535945008578981527552, 71600520613269560730058752,
    1841156244341217275915796480, 71600520613269560730058752, 1861613535945008578981527552, 1861613535945008578981527552, 61371874811373909197193216, 865397269818276833635860480,
    14538674132947050805082456064, 31500460621385276744345321472, 1038476723781932200363032576, 16615627580510915205808521216, 1211556177745587567090204672, 31500460621385276744345321472,
    31500460621385276744345321472, 16615627580510915205808521216, 388736453602369953669228527616, 31154301713457966010890977280, 14538674132947050805082456064, 31500460621385276744345321472,
    1211556177745587567090204672, 31154301713457966010890977280, 1211556177745587567090204672, 31500460621385276744345321472, 31500460621385276744345321472, 1038476723781932200363032576,
    29311991403914009318006980608, 2342917127879082819161423872, 995935589360236824336281894912, 57974736589859006780526297088, 1844424121947363070403674112, 995935345932390341646611382272,
    1894273422540535045279449088, 1894273422540535045279449088, 32053100281409579845123309568, 1744725520761019120652124160, 57974736589859006780526297088, 32053100281409579845123309568,
    29312234831760492007677493248, 1844424121947363070403674112, 1744725520761019120652124160, 2342917127879082819161423872, 47105605666624711006617600, 791374175199295144911175680,
    1714644046265139480640880640, 56526726799949653207941120, 904427628799194451327057920, 65947847933274595409264640, 1714644046265139480640880640, 1714644046265139480640880640,
    904427628799194451327057920, 21159838065447820184172625920, 1695801803998489596238233600, 791374175199295144911175680, 1714644046265139480640880640, 65947847933274595409264640,
    1695801803998489596238233600, 65947847933274595409264640, 1714644046265139480640880640, 1714644046265139480640880640
  ]
def negativeScales : Array ℕ := #[
    11, 20, 15, 14, 16, 12,
    15, 12, 16, 16, 11, 17,
    19, 21, 16, 16, 17, 21,
    21, 16, 25, 20, 19, 21,
    17, 20, 17, 21, 21, 16,
    29, 16, 34, 21, 16, 37,
    15, 15, 20, 16, 21, 20,
    32, 16, 16, 16, 13, 15,
    17, 12, 12, 13, 17, 17,
    12, 21, 16, 15, 17, 13,
    16, 13, 17, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11665780028361156, 20213959740008929, 15572670623940608, 14473134950387196, 16588612167811137, 12888172453193550,
    15572670623940608, 12888172453193550, 16588612167811137, 16588612167811137, 11665780028361156, 17483493036380206,
    19553882364272945, 21669359581725990, 16746527442422252, 16746527442422252, 17968919877847984, 21669359581725990,
    21669359581725990, 16746527442422252, 25294707153893291, 20653418037845600, 19553882364272945, 21669359581725990,
    17968919877847984, 20653418037845600, 17968919877847984, 21669359581725990, 21669359581725990, 16746527442422252,
    29565477642308537, 16920364493267946, 34651967192929391, 21549411016800793, 16575229000958025, 37651966840303987,
    15613703148778080, 15613703148778080, 20694450562717709, 16495058652271465, 21549411016800793, 20694450562717709,
    32565489623435436, 16575229000958025, 16495058652271465, 16920364493267946, 13284101125997071, 15354490453888470,
    17469967671308501, 12547135531832084, 12547135531832084, 13769527953509885, 17469967671308501, 17469967671308501,
    12547135531832084, 21095315243510310, 16454026127439437, 15354490453888470, 17469967671308501, 13769527953509885,
    16454026127439437, 13769527953509885, 17469967671308501, 17469967671308501
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
noncomputable def negativeCeiling : ℝ := 230493361 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 981949996981982547155091456, coefficient := (-981949996981982547155091456) }, { argument := 22973538471057633342815993856, coefficient := (-22973538471057633342815993856) }, { argument := 1841156244341217275915796480, coefficient := (-1841156244341217275915796480) }, { argument := 859206247359234728760705024, coefficient := (-859206247359234728760705024) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }, { argument := 71600520613269560730058752, coefficient := (-71600520613269560730058752) }, { argument := 1841156244341217275915796480, coefficient := (-1841156244341217275915796480) }, { argument := 71600520613269560730058752, coefficient := (-71600520613269560730058752) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }, { argument := 61371874811373909197193216, coefficient := (-61371874811373909197193216) }, { argument := 865397269818276833635860480, coefficient := (-865397269818276833635860480) }, { argument := 14538674132947050805082456064, coefficient := (-14538674132947050805082456064) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 1038476723781932200363032576, coefficient := (-1038476723781932200363032576) }, { argument := 16615627580510915205808521216, coefficient := (-16615627580510915205808521216) }, { argument := 1211556177745587567090204672, coefficient := (-1211556177745587567090204672) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 16615627580510915205808521216, coefficient := (-16615627580510915205808521216) }, { argument := 388736453602369953669228527616, coefficient := (-388736453602369953669228527616) }, { argument := 31154301713457966010890977280, coefficient := (-31154301713457966010890977280) }, { argument := 14538674132947050805082456064, coefficient := (-14538674132947050805082456064) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 1211556177745587567090204672, coefficient := (-1211556177745587567090204672) }, { argument := 31154301713457966010890977280, coefficient := (-31154301713457966010890977280) }, { argument := 1211556177745587567090204672, coefficient := (-1211556177745587567090204672) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 1038476723781932200363032576, coefficient := (-1038476723781932200363032576) }, { argument := 29311991403914009318006980608, coefficient := (-29311991403914009318006980608) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 995935589360236824336281894912, coefficient := (-995935589360236824336281894912) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 995935345932390341646611382272, coefficient := (-995935345932390341646611382272) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }, { argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }, { argument := 29312234831760492007677493248, coefficient := (-29312234831760492007677493248) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 47105605666624711006617600, coefficient := (-47105605666624711006617600) }, { argument := 791374175199295144911175680, coefficient := (-791374175199295144911175680) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }, { argument := 56526726799949653207941120, coefficient := (-56526726799949653207941120) }, { argument := 904427628799194451327057920, coefficient := (-904427628799194451327057920) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }, { argument := 904427628799194451327057920, coefficient := (-904427628799194451327057920) }, { argument := 21159838065447820184172625920, coefficient := (-21159838065447820184172625920) }, { argument := 1695801803998489596238233600, coefficient := (-1695801803998489596238233600) }, { argument := 791374175199295144911175680, coefficient := (-791374175199295144911175680) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 1695801803998489596238233600, coefficient := (-1695801803998489596238233600) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }, { argument := 1714644046265139480640880640, coefficient := (-1714644046265139480640880640) }] }

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

end TermShard5


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
