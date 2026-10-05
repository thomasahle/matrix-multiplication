import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 13, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 538361712187802739093735763901153280
def positiveArguments : Array ℕ := #[
    70799, 135, 105, 15, 141, 1665,
    117, 105, 1665, 15, 117, 117,
    117, 117, 117, 135, 141, 45,
    189
  ]
def positiveCoefficients : Array ℕ := #[
    5609274677847400837285318139838464, 5222559540735198034730680320, 4061990753905154027012751360, 4642275147320176030871715840, 5454673298101206836274266112, 64411567669067442428345057280,
    144838984596389492163197534208, 4061990753905154027012751360, 64411567669067442428345057280, 4642275147320176030871715840, 4526218268637171630099922944, 4526218268637171630099922944,
    4526218268637171630099922944, 144838984596389492163197534208, 4526218268637171630099922944, 5222559540735198034730680320, 5454673298101206836274266112, 1740853180245066011576893440,
    29246333428117108994491809792
  ]
def positiveScales : Array ℕ := #[
    16, 7, 6, 3, 7, 10,
    6, 6, 10, 3, 6, 6,
    6, 6, 6, 7, 7, 5,
    7
  ]
def negativeArguments : Array ℕ := #[
    362575341, 16929, 7587, 2565, 837, 6694228695,
    6693989673, 1372092467, 2565, 837, 4966752609, 8451,
    343023003, 16929, 7587, 2565, 837, 32993163549,
    32991626979, 531, 6694228695, 6693989673, 927, 1841539199,
    5415, 1767, 6649399653, 17841, 460384647, 35739,
    16017, 5415, 1767, 101822477547, 101819370261, 531,
    60512777451, 60509670165, 14409, 927, 284442805007531, 284442306677589,
    5407539, 489, 3
  ]
def negativeCoefficients : Array ℕ := #[
    6688334522864969812128301056, 319779768754000895290638336, 286628756044255985890492416, 387611840913940479140167680, 15810482984647572175454208, 7717920219221729720213176320,
    7717644645617855582435278848, 6327659646053442129565319168, 387611840913940479140167680, 15810482984647572175454208, 22905103563913050949247041536, 319269753173850973607559168,
    6327657547736303745103822848, 319779768754000895290638336, 286628756044255985890492416, 387611840913940479140167680, 15810482984647572175454208, 152154111042611436897536311296,
    152147024864226101926104662016, 20542067526891778936607342592, 7717920219221729720213176320, 7717644645617855582435278848, 17930787756524179919242002432, 8492600576414271160394448896,
    409145832075826061314621440, 16688843150461326185201664, 30664943410676024734553997312, 337006961683509361030201344, 8492597758674113901260439552, 337545311462556500584562688,
    302552575824492429551075328, 409145832075826061314621440, 16688843150461326185201664, 234786648032568266552449695744, 234779483118867538970224361472, 20542067526891778936607342592,
    139532964853492404619000676352, 139525799939791677036775342080, 278710594157235068453460639744, 17930787756524179919242002432, 160127063830016908159375900672, 160126783295199270814265376768,
    102145523713641753636897816576, 18917271225329717325802242048, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    28, 14, 12, 11, 9, 32,
    32, 30, 11, 9, 32, 13,
    28, 14, 12, 11, 9, 34,
    34, 9, 32, 32, 9, 30,
    12, 10, 32, 14, 28, 15,
    13, 12, 10, 36, 36, 9,
    35, 35, 13, 9, 48, 48,
    22, 8, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    16111441362665214, 7076815597050830, 6714245517659862, 3906890595303263, 7139551352398793, 10701306461953989,
    6870364719426147, 6714245517659862, 10701306461953989, 3906890595303263, 6870364719426147, 6870364719426147,
    6870364719426147, 6870364719426147, 6870364719426147, 7076815597050830, 7139551352398793, 5491853096329661,
    7562242424220952
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    28433705568828706, 14047209134965508, 12889313825985969, 11324743110494417, 9709083812639846, 32640270692673927,
    32640219179344107, 30353730563767537, 11324743110494417, 9709083812639846, 32209655742767162, 13044906349096087,
    28353730085354916, 14047209134965508, 12889313825985969, 11324743110494417, 9709083812639846, 34941448075217434,
    34941380883907365, 9052568050804154, 32640270692673927, 32640219179344107, 9856425530582692, 30778264961166772,
    12402745622495697, 10787086325046961, 32630576945479504, 14122908861097361, 28778264482498263, 15125211646966781,
    13967316348309272, 12402745622495697, 10787086325046961, 36567265118595482, 36567221091631950, 9052568050804154,
    35816520753631071, 35816446670413079, 13814682594827495, 9856425530582692, 48015131916886801, 48015129389353135,
    22366540734486686, 8933690662845865, 1584962500724866
  ]

abbrev PositiveTerm := Fin 19
abbrev NegativeTerm := Fin 45
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
noncomputable def positiveFloor : ℝ := 1087879182281 / 1000000000000
noncomputable def negativeCeiling : ℝ := 780367381 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6688334522864969812128301056, coefficient := (-6688334522864969812128301056) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 7717920219221729720213176320, coefficient := (-7717920219221729720213176320) }, { argument := 7717644645617855582435278848, coefficient := (-7717644645617855582435278848) }, { argument := 6327659646053442129565319168, coefficient := (-6327659646053442129565319168) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 22905103563913050949247041536, coefficient := (-22905103563913050949247041536) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }, { argument := 6327657547736303745103822848, coefficient := (-6327657547736303745103822848) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 152154111042611436897536311296, coefficient := (-152154111042611436897536311296) }, { argument := 152147024864226101926104662016, coefficient := (-152147024864226101926104662016) }, { argument := 20542067526891778936607342592, coefficient := (-20542067526891778936607342592) }, { argument := 7717920219221729720213176320, coefficient := (-7717920219221729720213176320) }, { argument := 7717644645617855582435278848, coefficient := (-7717644645617855582435278848) }, { argument := 17930787756524179919242002432, coefficient := (-17930787756524179919242002432) }, { argument := 8492600576414271160394448896, coefficient := (-8492600576414271160394448896) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 30664943410676024734553997312, coefficient := (-30664943410676024734553997312) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 8492597758674113901260439552, coefficient := (-8492597758674113901260439552) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 234786648032568266552449695744, coefficient := (-234786648032568266552449695744) }, { argument := 234779483118867538970224361472, coefficient := (-234779483118867538970224361472) }, { argument := 20542067526891778936607342592, coefficient := (-20542067526891778936607342592) }, { argument := 139532964853492404619000676352, coefficient := (-139532964853492404619000676352) }, { argument := 139525799939791677036775342080, coefficient := (-139525799939791677036775342080) }, { argument := 278710594157235068453460639744, coefficient := (-278710594157235068453460639744) }, { argument := 17930787756524179919242002432, coefficient := (-17930787756524179919242002432) }, { argument := 160127063830016908159375900672, coefficient := (-160127063830016908159375900672) }, { argument := 160126783295199270814265376768, coefficient := (-160126783295199270814265376768) }, { argument := 102145523713641753636897816576, coefficient := (-102145523713641753636897816576) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }, { argument := 5609274677847400837285318139838464, coefficient := 5609274677847400837285318139838464 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 144838984596389492163197534208, coefficient := 144838984596389492163197534208 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 144838984596389492163197534208, coefficient := 144838984596389492163197534208 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 29246333428117108994491809792, coefficient := 29246333428117108994491809792 }] }

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


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 202736726249657891729104510715428864
def positiveArguments : Array ℕ := #[
    819, 27, 27, 63, 819, 819,
    27, 10107, 405, 189, 819, 63,
    405, 63, 819, 819, 27, 3,
    57, 87, 897, 27, 87, 27,
    27, 2313, 27, 897, 2313, 3,
    27, 27, 57, 405, 25245527459, 25245504093,
    179653744651, 285, 93, 309830121929, 939, 179653743715,
    1881, 843, 285, 93, 6542974639, 4935,
    29721567029, 122115, 3885, 475536176389, 1995, 1995,
    67515, 3675, 122115, 67515, 13094861389
  ]
def positiveCoefficients : Array ℕ := #[
    63367055760920402821398921216, 2089023816294079213892272128, 33424381060705267422276354048, 2437194452343092416207650816, 63367055760920402821398921216, 63367055760920402821398921216,
    33424381060705267422276354048, 781991248566083652400340533248, 62670714488822376416768163840, 29246333428117108994491809792, 63367055760920402821398921216, 2437194452343092416207650816,
    62670714488822376416768163840, 2437194452343092416207650816, 63367055760920402821398921216, 63367055760920402821398921216, 2089023816294079213892272128, 3713820117856140824697372672,
    4410161389954167229328130048, 3365649481807127622381993984, 34701006726218315830766075904, 4178047632588158427784544256, 3365649481807127622381993984, 4178047632588158427784544256,
    4178047632588158427784544256, 178959706929192785990104645632, 4178047632588158427784544256, 34701006726218315830766075904, 178959706929192785990104645632, 3713820117856140824697372672,
    4178047632588158427784544256, 4178047632588158427784544256, 4410161389954167229328130048, 32087405818277056725385299886080, 476874530858987525439801163513856, 476874089487726570511280910630912,
    848390822261904206940305511940096, 88203227799083344586562600960, 3597763239173136423925579776, 2926262766361850132744805881479168, 72651606055560754883142352896, 848390817841769178974317591920640,
    72767662934243759283914145792, 65223965819848473233747607552, 88203227799083344586562600960, 3597763239173136423925579776, 61796648266959433152281326911488, 95456782716771119634799656960,
    2245698111297810247813035085266944, 2362047623395847066707914915840, 75146828947245349499735900160, 2245656100771401153233990654623744, 77177824324197926513242275840, 77177824324197926513242275840,
    1305930027380507019684599562240, 71084838193340195472723148800, 2362047623395847066707914915840, 1305930027380507019684599562240, 61838734521237447028956404383744
  ]
def positiveScales : Array ℕ := #[
    9, 4, 4, 5, 9, 9,
    4, 13, 8, 7, 9, 5,
    8, 5, 9, 9, 4, 1,
    5, 6, 9, 4, 6, 4,
    4, 11, 4, 9, 11, 1,
    4, 4, 5, 8, 34, 34,
    37, 8, 6, 38, 9, 37,
    10, 9, 8, 6, 32, 12,
    34, 16, 11, 38, 10, 10,
    16, 11, 16, 16, 33
  ]
def negativeArguments : Array ℕ := #[
    9, 3, 405, 6019, 14589
  ]
def negativeCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 475368975085586025561263702016, 32087405818277056725385299886080, 953748620346714095951082074144768, 4623438651682409684608850765807616
  ]
def negativeScales : Array ℕ := #[
    3, 1, 8, 12, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9677719641638369, 4754887502147955, 4754887502147955, 5977279922488012, 9677719641638369, 9677719641638369,
    4754887502147955, 13303067213842913, 8661778097770205, 7562242424220952, 9677719641638369, 5977279922488012,
    8661778097770205, 5977279922488012, 9677719641638369, 9677719641638369, 4754887502147955, 1584962500720924,
    5832890014087662, 6442943495848725, 9808964174871270, 4754887502147955, 6442943495848725, 4754887502147955,
    4754887502147955, 11175549550636190, 4754887502147955, 9808964174871270, 11175549550636190, 1584962500720924,
    4754887502147955, 4754887502147955, 5832890014087662, 8661778097770205, 34555308769044641, 34555307433757511,
    37386428050535096, 8154818109052103, 6539158811107971, 38172686454657581, 9874981347482478, 37386428043018623,
    10877284133344468, 9719388820935039, 8154818109052103, 6539158811107971, 32607299532715630, 12268834369343759,
    34790791130846492, 16897880898879436, 11923698882884927, 38790764141936148, 10962173030320774, 10962173030320774,
    16042920444994069, 11843528534516384, 16897880898879436, 16042920444994069, 33608281737507037
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 1584962500724866, 8661778097800657, 12555308101402890, 13832593378197645
  ]

abbrev PositiveTerm := Fin 59
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
noncomputable def positiveFloor : ℝ := 2274157389029 / 500000000000
noncomputable def negativeCeiling : ℝ := 183473626453 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 63367055760920402821398921216, coefficient := 63367055760920402821398921216 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 2437194452343092416207650816, coefficient := 2437194452343092416207650816 }, { argument := 63367055760920402821398921216, coefficient := 63367055760920402821398921216 }, { argument := 63367055760920402821398921216, coefficient := 63367055760920402821398921216 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 781991248566083652400340533248, coefficient := 781991248566083652400340533248 }, { argument := 62670714488822376416768163840, coefficient := 62670714488822376416768163840 }, { argument := 29246333428117108994491809792, coefficient := 29246333428117108994491809792 }, { argument := 63367055760920402821398921216, coefficient := 63367055760920402821398921216 }, { argument := 2437194452343092416207650816, coefficient := 2437194452343092416207650816 }, { argument := 62670714488822376416768163840, coefficient := 62670714488822376416768163840 }, { argument := 2437194452343092416207650816, coefficient := 2437194452343092416207650816 }, { argument := 63367055760920402821398921216, coefficient := 63367055760920402821398921216 }, { argument := 63367055760920402821398921216, coefficient := 63367055760920402821398921216 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 178959706929192785990104645632, coefficient := 178959706929192785990104645632 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 178959706929192785990104645632, coefficient := 178959706929192785990104645632 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 32087405818277056725385299886080, coefficient := 32087405818277056725385299886080 }, { argument := 32087405818277056725385299886080, coefficient := (-32087405818277056725385299886080) }, { argument := 476874530858987525439801163513856, coefficient := 476874530858987525439801163513856 }, { argument := 476874089487726570511280910630912, coefficient := 476874089487726570511280910630912 }, { argument := 953748620346714095951082074144768, coefficient := (-953748620346714095951082074144768) }, { argument := 848390822261904206940305511940096, coefficient := 848390822261904206940305511940096 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 2926262766361850132744805881479168, coefficient := 2926262766361850132744805881479168 }, { argument := 72651606055560754883142352896, coefficient := 72651606055560754883142352896 }, { argument := 848390817841769178974317591920640, coefficient := 848390817841769178974317591920640 }, { argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 65223965819848473233747607552, coefficient := 65223965819848473233747607552 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4623438651682409684608850765807616, coefficient := (-4623438651682409684608850765807616) }, { argument := 61796648266959433152281326911488, coefficient := 61796648266959433152281326911488 }, { argument := 95456782716771119634799656960, coefficient := 95456782716771119634799656960 }, { argument := 2245698111297810247813035085266944, coefficient := 2245698111297810247813035085266944 }, { argument := 2362047623395847066707914915840, coefficient := 2362047623395847066707914915840 }, { argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 2245656100771401153233990654623744, coefficient := 2245656100771401153233990654623744 }, { argument := 77177824324197926513242275840, coefficient := 77177824324197926513242275840 }, { argument := 77177824324197926513242275840, coefficient := 77177824324197926513242275840 }, { argument := 1305930027380507019684599562240, coefficient := 1305930027380507019684599562240 }, { argument := 71084838193340195472723148800, coefficient := 71084838193340195472723148800 }, { argument := 2362047623395847066707914915840, coefficient := 2362047623395847066707914915840 }, { argument := 1305930027380507019684599562240, coefficient := 1305930027380507019684599562240 }, { argument := 61838734521237447028956404383744, coefficient := 61838734521237447028956404383744 }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
