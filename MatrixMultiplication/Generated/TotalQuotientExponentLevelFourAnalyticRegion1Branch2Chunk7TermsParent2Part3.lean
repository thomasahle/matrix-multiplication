import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

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
def constantNumerator : ℤ := (-12804699800128754406162756723015680)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    31848762141, 1196639810787, 2393098612773, 63878533083, 653672188635, 158175,
    51615, 1122197319717, 521145, 653672188635, 1043955, 467865,
    158175, 51615, 38982573, 1464675411, 2929129269, 78186699,
    177998829243, 11115, 3627, 306027972933, 36621, 177998829243,
    73359, 32877, 11115, 3627, 14529, 14529,
    35857515688457, 3254132578672243, 32083699293, 31731571420522785, 32922488817, 1048486905,
    32083699293, 18243672147, 32922488817, 513968280831, 629092143, 1627067034810925,
    32083699293, 1048486905, 629092143, 1048486905, 16146698337, 18243672147,
    35857474400777, 810525184803441, 1693318867, 14330905313316369, 41900634943, 1333038257,
    57323255316882581, 684533159, 684533159, 23166043223, 1260982135, 41900634943,
    23166043223, 1621420451601989, 1333038257, 1260982135
  ]
def negativeCoefficients : Array ℕ := #[
    1175011928558953761875492339712, 44148216676000022853929700163584, 44144877652972886832369440391168, 1178350951586089783435752112128, 6029061785925719184067610542080, 5975682547423249053410918400,
    243744946013316737704919040, 20700886757022312709017066012672, 4922075361430202509783203840, 6029061785925719184067610542080, 4929938101624180469064007680, 4418859989015613115811758080,
    5975682547423249053410918400, 243744946013316737704919040, 46022499037804798506751229952, 1729183517297430515698592907264, 1729052735489758113385339158528, 46153280845477200820004978688,
    1641749424232774341837239353344, 13437210485016603276859146240, 548096743467782502082412544, 5645219696091164818844814409728, 11068018110026833751728717824, 1641749424232774341837239353344,
    11085698650138697703408795648, 9936463542867540844203737088, 13437210485016603276859146240, 548096743467782502082412544, 140515865865447578234448248832, 140515865865447578234448248832,
    10092993393310416221128097792, 915956891795156552120069521408, 73979973724478385133700775936, 8931643326584168434751200296960, 75914090684595467097980534784, 2417646200146352455349698560,
    73979973724478385133700775936, 42067043882546532723084754944, 75914090684595467097980534784, 1185130167311741973612422234112, 46418807042809967142714212352, 915957311460162459206785433600,
    73979973724478385133700775936, 2417646200146352455349698560, 46418807042809967142714212352, 2417646200146352455349698560, 74463502964507655624770715648, 42067043882546532723084754944,
    10092981771861649784110579712, 912570230063794823696360669184, 15618109887366411214741569536, 32270329914466730328178412224512, 386465144659726303037115858944, 12295107783671430105222086656,
    32270123910597024424535126966272, 12627407994040928216174034944, 12627407994040928216174034944, 213669035267587285342102749184, 11630507362932433883318190080, 386465144659726303037115858944,
    213669035267587285342102749184, 912778567705702375561854189568, 12295107783671430105222086656, 11630507362932433883318190080
  ]
def negativeScales : Array ℕ := #[
    34, 40, 41, 35, 39, 17,
    15, 40, 18, 39, 19, 18,
    17, 15, 25, 30, 31, 26,
    37, 13, 11, 38, 15, 37,
    16, 15, 13, 11, 13, 13,
    45, 51, 34, 54, 34, 29,
    34, 34, 34, 38, 29, 50,
    34, 29, 29, 29, 33, 34,
    45, 49, 30, 53, 35, 30,
    55, 29, 29, 34, 30, 35,
    34, 50, 30, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34890518253207641, 40122126104304895, 41122016986100315, 35894612135684322, 39249776360835145, 17271162070289573,
    15655502772369993, 40029463510805649, 18991325329495353, 39249776360835145, 19993628116142017, 18835732783495415,
    17271162070289573, 15655502772369993, 25216325981380777, 30447933836159254, 31447824717954675, 26220419863574444,
    37373076795902815, 13440220327914385, 11824561031027542, 38154872574349645, 15160383566516023, 37373076795902815,
    16162686352385444, 15004791039804331, 13440220327914385, 11824561031027542, 13826647789424418, 13826647789424418,
    45027340771153635, 51531194453269556, 34901121449361341, 54816768487710587, 34938354359655640, 29965661710646952,
    34901121449361341, 34086677098061165, 34938354359655640, 38902888375678595, 29228696102933592, 50531195114270625,
    34901121449361341, 29965661710646952, 29228696102933592, 29965661710646952, 33910520148175159, 34086677098061165,
    45027339109979838, 49525850342576804, 30657206525132694, 53669979268780437, 35286253054902709, 30312071039058440,
    55669970059029222, 29350545186873076, 29350545186873076, 34431292600757460, 30231900690374457, 35286253054902709,
    34431292600757460, 50526179668878154, 30312071039058440, 30231900690374457
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
noncomputable def negativeCeiling : ℝ := 58623411749 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1175011928558953761875492339712, coefficient := (-1175011928558953761875492339712) }, { argument := 44148216676000022853929700163584, coefficient := (-44148216676000022853929700163584) }, { argument := 44144877652972886832369440391168, coefficient := (-44144877652972886832369440391168) }, { argument := 1178350951586089783435752112128, coefficient := (-1178350951586089783435752112128) }, { argument := 6029061785925719184067610542080, coefficient := (-6029061785925719184067610542080) }, { argument := 5975682547423249053410918400, coefficient := (-5975682547423249053410918400) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }, { argument := 20700886757022312709017066012672, coefficient := (-20700886757022312709017066012672) }, { argument := 4922075361430202509783203840, coefficient := (-4922075361430202509783203840) }, { argument := 6029061785925719184067610542080, coefficient := (-6029061785925719184067610542080) }, { argument := 4929938101624180469064007680, coefficient := (-4929938101624180469064007680) }, { argument := 4418859989015613115811758080, coefficient := (-4418859989015613115811758080) }, { argument := 5975682547423249053410918400, coefficient := (-5975682547423249053410918400) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }, { argument := 46022499037804798506751229952, coefficient := (-46022499037804798506751229952) }, { argument := 1729183517297430515698592907264, coefficient := (-1729183517297430515698592907264) }, { argument := 1729052735489758113385339158528, coefficient := (-1729052735489758113385339158528) }, { argument := 46153280845477200820004978688, coefficient := (-46153280845477200820004978688) }, { argument := 1641749424232774341837239353344, coefficient := (-1641749424232774341837239353344) }, { argument := 13437210485016603276859146240, coefficient := (-13437210485016603276859146240) }, { argument := 548096743467782502082412544, coefficient := (-548096743467782502082412544) }, { argument := 5645219696091164818844814409728, coefficient := (-5645219696091164818844814409728) }, { argument := 11068018110026833751728717824, coefficient := (-11068018110026833751728717824) }, { argument := 1641749424232774341837239353344, coefficient := (-1641749424232774341837239353344) }, { argument := 11085698650138697703408795648, coefficient := (-11085698650138697703408795648) }, { argument := 9936463542867540844203737088, coefficient := (-9936463542867540844203737088) }, { argument := 13437210485016603276859146240, coefficient := (-13437210485016603276859146240) }, { argument := 548096743467782502082412544, coefficient := (-548096743467782502082412544) }, { argument := 140515865865447578234448248832, coefficient := (-140515865865447578234448248832) }, { argument := 140515865865447578234448248832, coefficient := (-140515865865447578234448248832) }, { argument := 10092993393310416221128097792, coefficient := (-10092993393310416221128097792) }, { argument := 915956891795156552120069521408, coefficient := (-915956891795156552120069521408) }, { argument := 73979973724478385133700775936, coefficient := (-73979973724478385133700775936) }, { argument := 8931643326584168434751200296960, coefficient := (-8931643326584168434751200296960) }, { argument := 75914090684595467097980534784, coefficient := (-75914090684595467097980534784) }, { argument := 2417646200146352455349698560, coefficient := (-2417646200146352455349698560) }, { argument := 73979973724478385133700775936, coefficient := (-73979973724478385133700775936) }, { argument := 42067043882546532723084754944, coefficient := (-42067043882546532723084754944) }, { argument := 75914090684595467097980534784, coefficient := (-75914090684595467097980534784) }, { argument := 1185130167311741973612422234112, coefficient := (-1185130167311741973612422234112) }, { argument := 46418807042809967142714212352, coefficient := (-46418807042809967142714212352) }, { argument := 915957311460162459206785433600, coefficient := (-915957311460162459206785433600) }, { argument := 73979973724478385133700775936, coefficient := (-73979973724478385133700775936) }, { argument := 2417646200146352455349698560, coefficient := (-2417646200146352455349698560) }, { argument := 46418807042809967142714212352, coefficient := (-46418807042809967142714212352) }, { argument := 2417646200146352455349698560, coefficient := (-2417646200146352455349698560) }, { argument := 74463502964507655624770715648, coefficient := (-74463502964507655624770715648) }, { argument := 42067043882546532723084754944, coefficient := (-42067043882546532723084754944) }, { argument := 10092981771861649784110579712, coefficient := (-10092981771861649784110579712) }, { argument := 912570230063794823696360669184, coefficient := (-912570230063794823696360669184) }, { argument := 15618109887366411214741569536, coefficient := (-15618109887366411214741569536) }, { argument := 32270329914466730328178412224512, coefficient := (-32270329914466730328178412224512) }, { argument := 386465144659726303037115858944, coefficient := (-386465144659726303037115858944) }, { argument := 12295107783671430105222086656, coefficient := (-12295107783671430105222086656) }, { argument := 32270123910597024424535126966272, coefficient := (-32270123910597024424535126966272) }, { argument := 12627407994040928216174034944, coefficient := (-12627407994040928216174034944) }, { argument := 12627407994040928216174034944, coefficient := (-12627407994040928216174034944) }, { argument := 213669035267587285342102749184, coefficient := (-213669035267587285342102749184) }, { argument := 11630507362932433883318190080, coefficient := (-11630507362932433883318190080) }, { argument := 386465144659726303037115858944, coefficient := (-386465144659726303037115858944) }, { argument := 213669035267587285342102749184, coefficient := (-213669035267587285342102749184) }, { argument := 912778567705702375561854189568, coefficient := (-912778567705702375561854189568) }, { argument := 12295107783671430105222086656, coefficient := (-12295107783671430105222086656) }, { argument := 11630507362932433883318190080, coefficient := (-11630507362932433883318190080) }] }

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
def constantNumerator : ℤ := (-4262399546384818358512811761467392)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1693318867, 649977368482749, 9975, 3255, 8825571117380595, 32865,
    2599909368233241, 65835, 29505, 9975, 3255, 1988111223,
    74698445961, 149385592719, 3987521649, 653672188635, 158175, 51615,
    1122197319717, 521145, 653672188635, 1043955, 467865, 158175,
    51615, 112525213, 112525213, 15768687315, 1425, 465,
    27081872685, 4695, 15768687315, 9405, 4215, 1425,
    465, 23403, 23403, 535, 4185, 3255,
    465, 4371, 51615, 3627, 3255, 51615,
    465, 3627, 3627, 3627, 3627, 3627,
    4185, 4371, 8512035, 1358922495, 54240011805, 1358922495,
    34044255, 64970955, 2441125685, 4881882115
  ]
def negativeCoefficients : Array ℕ := #[
    15618109887366411214741569536, 5854475668996327934896015147008, 376844845332997688052940800, 15371302901740695170580480, 19873419397783529827871552962560, 310401148919021779896238080,
    5854475430986142918947024928768, 310896997399723092643676160, 278666846154137764060200960, 376844845332997688052940800, 15371302901740695170580480, 73348357841501397620134772736,
    2755886230692779884394632445952, 2755677797186801993207884283904, 73556791347479288806882934784, 6029061785925719184067610542080, 5975682547423249053410918400, 243744946013316737704919040,
    20700886757022312709017066012672, 4922075361430202509783203840, 6029061785925719184067610542080, 4929938101624180469064007680, 4418859989015613115811758080, 5975682547423249053410918400,
    243744946013316737704919040, 531385294348967678905572917248, 531385294348967678905572917248, 145440469639077615780778475520, 430679823237711643489075200, 17567203316275080194949120,
    499572374456980332532948008960, 354744170193167748452843520, 145440469639077615780778475520, 355310854171112105878487040, 318476395604728873211658240, 430679823237711643489075200,
    17567203316275080194949120, 226339927651529332605189095424, 226339927651529332605189095424, 20696810031802451470969733120, 19763103730809465219317760, 15371302901740695170580480,
    17567203316275080194949120, 20641463896623219229065216, 243744946013316737704919040, 548096743467782502082412544, 15371302901740695170580480, 243744946013316737704919040,
    17567203316275080194949120, 17128023233368203190075392, 17128023233368203190075392, 17128023233368203190075392, 548096743467782502082412544, 17128023233368203190075392,
    19763103730809465219317760, 20641463896623219229065216, 78509665595729141594849280, 12533847740635923893673000960, 125068952040227483724137103360, 12533847740635923893673000960,
    78500707395638346393845760, 2397005158218999922226626560, 90061641525907839359301713920, 90054829973424901738819747840
  ]
def negativeScales : Array ℕ := #[
    30, 49, 13, 11, 52, 15,
    51, 16, 14, 13, 11, 30,
    36, 37, 31, 39, 17, 15,
    40, 18, 39, 19, 18, 17,
    15, 26, 26, 33, 10, 8,
    34, 12, 33, 13, 12, 10,
    8, 14, 14, 9, 12, 11,
    8, 12, 15, 11, 11, 15,
    8, 11, 11, 11, 11, 11,
    12, 12, 23, 30, 35, 30,
    25, 25, 31, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30657206525132694, 49207382814339358, 13284101125997071, 11668441828086828, 52970611078612195, 15004264364598741,
    51207382755687458, 16006567150468162, 14848671839575775, 13284101125997071, 11668441828086828, 30888751326917220,
    36120359178130707, 37120250059926127, 31892845209385586, 39249776360835145, 17271162070289573, 15655502772369993,
    40029463510805649, 18991325329495353, 39249776360835145, 19993628116142017, 18835732783495415, 17271162070289573,
    15655502772369993, 26745673054920054, 26745673054920054, 33876343517805173, 10476746203939589, 8861086908132560,
    34656608452211647, 12196909442541137, 33876343517805173, 13199212228410558, 12041316915829445, 10476746203939589,
    8861086908132560, 14514405858405788, 14514405858405788, 9063395081288510, 12031011907437707, 11668441828086828,
    8861086908132560, 12093747662785669, 15655502772369993, 11824561031027542, 11668441828086828, 15655502772369993,
    8861086908132560, 11824561031027542, 11824561031027542, 11824561031027542, 11824561031027542, 11824561031027542,
    12031011907437707, 12093747662785669, 23021072652285295, 30339816029541345, 35658638441367988, 30339816029541345,
    25020908026845408, 25953291586565642, 31184899430325417, 32184790312120838
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
noncomputable def negativeCeiling : ℝ := 2424967251 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 15618109887366411214741569536, coefficient := (-15618109887366411214741569536) }, { argument := 5854475668996327934896015147008, coefficient := (-5854475668996327934896015147008) }, { argument := 376844845332997688052940800, coefficient := (-376844845332997688052940800) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 19873419397783529827871552962560, coefficient := (-19873419397783529827871552962560) }, { argument := 310401148919021779896238080, coefficient := (-310401148919021779896238080) }, { argument := 5854475430986142918947024928768, coefficient := (-5854475430986142918947024928768) }, { argument := 310896997399723092643676160, coefficient := (-310896997399723092643676160) }, { argument := 278666846154137764060200960, coefficient := (-278666846154137764060200960) }, { argument := 376844845332997688052940800, coefficient := (-376844845332997688052940800) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 73348357841501397620134772736, coefficient := (-73348357841501397620134772736) }, { argument := 2755886230692779884394632445952, coefficient := (-2755886230692779884394632445952) }, { argument := 2755677797186801993207884283904, coefficient := (-2755677797186801993207884283904) }, { argument := 73556791347479288806882934784, coefficient := (-73556791347479288806882934784) }, { argument := 6029061785925719184067610542080, coefficient := (-6029061785925719184067610542080) }, { argument := 5975682547423249053410918400, coefficient := (-5975682547423249053410918400) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }, { argument := 20700886757022312709017066012672, coefficient := (-20700886757022312709017066012672) }, { argument := 4922075361430202509783203840, coefficient := (-4922075361430202509783203840) }, { argument := 6029061785925719184067610542080, coefficient := (-6029061785925719184067610542080) }, { argument := 4929938101624180469064007680, coefficient := (-4929938101624180469064007680) }, { argument := 4418859989015613115811758080, coefficient := (-4418859989015613115811758080) }, { argument := 5975682547423249053410918400, coefficient := (-5975682547423249053410918400) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }, { argument := 531385294348967678905572917248, coefficient := (-531385294348967678905572917248) }, { argument := 531385294348967678905572917248, coefficient := (-531385294348967678905572917248) }, { argument := 145440469639077615780778475520, coefficient := (-145440469639077615780778475520) }, { argument := 430679823237711643489075200, coefficient := (-430679823237711643489075200) }, { argument := 17567203316275080194949120, coefficient := (-17567203316275080194949120) }, { argument := 499572374456980332532948008960, coefficient := (-499572374456980332532948008960) }, { argument := 354744170193167748452843520, coefficient := (-354744170193167748452843520) }, { argument := 145440469639077615780778475520, coefficient := (-145440469639077615780778475520) }, { argument := 355310854171112105878487040, coefficient := (-355310854171112105878487040) }, { argument := 318476395604728873211658240, coefficient := (-318476395604728873211658240) }, { argument := 430679823237711643489075200, coefficient := (-430679823237711643489075200) }, { argument := 17567203316275080194949120, coefficient := (-17567203316275080194949120) }, { argument := 226339927651529332605189095424, coefficient := (-226339927651529332605189095424) }, { argument := 226339927651529332605189095424, coefficient := (-226339927651529332605189095424) }, { argument := 20696810031802451470969733120, coefficient := (-20696810031802451470969733120) }, { argument := 19763103730809465219317760, coefficient := (-19763103730809465219317760) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 17567203316275080194949120, coefficient := (-17567203316275080194949120) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }, { argument := 548096743467782502082412544, coefficient := (-548096743467782502082412544) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }, { argument := 17567203316275080194949120, coefficient := (-17567203316275080194949120) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 548096743467782502082412544, coefficient := (-548096743467782502082412544) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 19763103730809465219317760, coefficient := (-19763103730809465219317760) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 78509665595729141594849280, coefficient := (-78509665595729141594849280) }, { argument := 12533847740635923893673000960, coefficient := (-12533847740635923893673000960) }, { argument := 125068952040227483724137103360, coefficient := (-125068952040227483724137103360) }, { argument := 12533847740635923893673000960, coefficient := (-12533847740635923893673000960) }, { argument := 78500707395638346393845760, coefficient := (-78500707395638346393845760) }, { argument := 2397005158218999922226626560, coefficient := (-2397005158218999922226626560) }, { argument := 90061641525907839359301713920, coefficient := (-90061641525907839359301713920) }, { argument := 90054829973424901738819747840, coefficient := (-90054829973424901738819747840) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
