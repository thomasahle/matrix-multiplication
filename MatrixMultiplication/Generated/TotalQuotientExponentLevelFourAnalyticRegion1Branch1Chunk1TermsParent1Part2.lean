import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2650448130399985198133364125597696)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    20908045125, 105417915, 405772835, 16624588175, 342313144225, 16624588175,
    405772835, 340827165, 3406551705, 6813101745, 340827165, 1490573123,
    61069056815, 1257459170305, 61069056815, 1490573123, 278455793805, 2783152742985,
    5566304125665, 278455793805, 11948660025, 87052217425, 23897336125, 17836621635,
    178276205895, 356552324655, 17836621635, 21611651025, 157452144425, 43223331125,
    380655967, 160572037, 1119100367, 27010419915, 43601313, 72668855,
    2223666963, 72668855, 43601313, 35622272721, 2281802047, 160572037,
    2223666963, 72668855, 2281802047, 72668855, 2223666963, 72668855,
    380655967, 20194930025, 363793325, 101284582245, 4105667525, 363793325,
    202569116205, 363793325, 363793325, 15081831845, 93546855, 4105667525,
    15081831845, 20194930025, 363793325, 93546855
  ]
def negativeCoefficients : Array ℕ := #[
    24105334843902851958177792000, 121538581174316702933975040, 935648454913571715725393920, 153334761697521570089952870400, 1578640741146350443271972454400, 153334761697521570089952870400,
    935648454913571715725393920, 12574302972245955021404897280, 502718299807951349858162442240, 502718176952635818952548679680, 12574302972245955021404897280, 3437027615391373568398852096,
    563262630944566577722839531520, 5799006874438872134652232990720, 563262630944566577722839531520, 3437027615391373568398852096, 321037672760154539140243783680, 12835026591971757901066209853440,
    12835023455321983252632258478080, 321037672760154539140243783680, 110206936752469486427386675200, 401457493971973528393823027200, 110207010885322232647647232000, 20564224652527238941255925760,
    822153886144253770080536494080, 822153685224623162245313986560, 20564224652527238941255925760, 199332297734248853367108403200, 726119853016182291636106035200, 199332431819019839143411712000,
    877732900422428580940611584, 23696250175465766794702094336, 20643758062843434264871043072, 124563575873858175223631708160, 12868836195019283697581948928, 670251885157254359249059840,
    20509707685811983393021231104, 21448060325032139495969914880, 12868836195019283697581948928, 328557474104086086903889133568, 21045909193937786880420478976, 23696250175465766794702094336,
    20509707685811983393021231104, 670251885157254359249059840, 21045909193937786880420478976, 670251885157254359249059840, 20509707685811983393021231104, 21448060325032139495969914880,
    877732900422428580940611584, 23283169109852989816202854400, 13421604723997685733287526400, 467092691821525355723206164480, 151472396170831024704244940800, 13421604723997685733287526400,
    467092580483895655839993692160, 13421604723997685733287526400, 13421604723997685733287526400, 556421384414875485685720023040, 13805079144683333897095741440, 151472396170831024704244940800,
    556421384414875485685720023040, 23283169109852989816202854400, 13421604723997685733287526400, 13805079144683333897095741440
  ]
def negativeScales : Array ℕ := #[
    34, 26, 28, 33, 38, 33,
    28, 28, 31, 32, 28, 30,
    35, 40, 35, 30, 38, 41,
    42, 38, 33, 36, 34, 34,
    37, 38, 34, 34, 37, 35,
    28, 27, 30, 34, 25, 26,
    31, 26, 25, 35, 31, 27,
    31, 26, 31, 26, 31, 26,
    28, 34, 28, 36, 31, 28,
    37, 28, 28, 33, 26, 31,
    33, 34, 28, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34283339126998601, 26651544822352109, 28596097044300573, 33952599562318741, 38316525734134283, 33952599562318741,
    28596097044300573, 28344465086590259, 31665664958327022, 32665664605758245, 28344465086590259, 30473220005297887,
    35829722513600130, 40193648695136562, 35829722513600130, 30473220005297887, 38018657354735941, 41339857226441124,
    42339856873872347, 38018657354735941, 33476129786018619, 36341161996058522, 34476130756475345, 34054123334760729,
    37375323206465913, 38375322853897136, 34054123334760729, 34331090240163770, 37196122450203793, 35331091210620497,
    28503912452548525, 27258645434059150, 30059692284831217, 34652797017643007, 25377868244857474, 26114833839023678,
    31050293586828967, 26114833839023678, 25377868244857474, 35052060513003155, 31087526493027943, 27258645434059150,
    31050293586828967, 26114833839023678, 31087526493027943, 26114833839023678, 31050293586828967, 26114833839023678,
    28503912452548525, 34233274096015867, 28438543831286392, 36559623624500611, 31934969665475077, 28438543831286392,
    37559623280615408, 28438543831286392, 28438543831286392, 33812092619233149, 26479185815783841, 31934969665475077,
    33812092619233149, 34233274096015867, 28438543831286392, 26479185815783841
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
noncomputable def negativeCeiling : ℝ := 10307238189 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24105334843902851958177792000, coefficient := (-24105334843902851958177792000) }, { argument := 121538581174316702933975040, coefficient := (-121538581174316702933975040) }, { argument := 935648454913571715725393920, coefficient := (-935648454913571715725393920) }, { argument := 153334761697521570089952870400, coefficient := (-153334761697521570089952870400) }, { argument := 1578640741146350443271972454400, coefficient := (-1578640741146350443271972454400) }, { argument := 153334761697521570089952870400, coefficient := (-153334761697521570089952870400) }, { argument := 935648454913571715725393920, coefficient := (-935648454913571715725393920) }, { argument := 12574302972245955021404897280, coefficient := (-12574302972245955021404897280) }, { argument := 502718299807951349858162442240, coefficient := (-502718299807951349858162442240) }, { argument := 502718176952635818952548679680, coefficient := (-502718176952635818952548679680) }, { argument := 12574302972245955021404897280, coefficient := (-12574302972245955021404897280) }, { argument := 3437027615391373568398852096, coefficient := (-3437027615391373568398852096) }, { argument := 563262630944566577722839531520, coefficient := (-563262630944566577722839531520) }, { argument := 5799006874438872134652232990720, coefficient := (-5799006874438872134652232990720) }, { argument := 563262630944566577722839531520, coefficient := (-563262630944566577722839531520) }, { argument := 3437027615391373568398852096, coefficient := (-3437027615391373568398852096) }, { argument := 321037672760154539140243783680, coefficient := (-321037672760154539140243783680) }, { argument := 12835026591971757901066209853440, coefficient := (-12835026591971757901066209853440) }, { argument := 12835023455321983252632258478080, coefficient := (-12835023455321983252632258478080) }, { argument := 321037672760154539140243783680, coefficient := (-321037672760154539140243783680) }, { argument := 110206936752469486427386675200, coefficient := (-110206936752469486427386675200) }, { argument := 401457493971973528393823027200, coefficient := (-401457493971973528393823027200) }, { argument := 110207010885322232647647232000, coefficient := (-110207010885322232647647232000) }, { argument := 20564224652527238941255925760, coefficient := (-20564224652527238941255925760) }, { argument := 822153886144253770080536494080, coefficient := (-822153886144253770080536494080) }, { argument := 822153685224623162245313986560, coefficient := (-822153685224623162245313986560) }, { argument := 20564224652527238941255925760, coefficient := (-20564224652527238941255925760) }, { argument := 199332297734248853367108403200, coefficient := (-199332297734248853367108403200) }, { argument := 726119853016182291636106035200, coefficient := (-726119853016182291636106035200) }, { argument := 199332431819019839143411712000, coefficient := (-199332431819019839143411712000) }, { argument := 877732900422428580940611584, coefficient := (-877732900422428580940611584) }, { argument := 23696250175465766794702094336, coefficient := (-23696250175465766794702094336) }, { argument := 20643758062843434264871043072, coefficient := (-20643758062843434264871043072) }, { argument := 124563575873858175223631708160, coefficient := (-124563575873858175223631708160) }, { argument := 12868836195019283697581948928, coefficient := (-12868836195019283697581948928) }, { argument := 670251885157254359249059840, coefficient := (-670251885157254359249059840) }, { argument := 20509707685811983393021231104, coefficient := (-20509707685811983393021231104) }, { argument := 21448060325032139495969914880, coefficient := (-21448060325032139495969914880) }, { argument := 12868836195019283697581948928, coefficient := (-12868836195019283697581948928) }, { argument := 328557474104086086903889133568, coefficient := (-328557474104086086903889133568) }, { argument := 21045909193937786880420478976, coefficient := (-21045909193937786880420478976) }, { argument := 23696250175465766794702094336, coefficient := (-23696250175465766794702094336) }, { argument := 20509707685811983393021231104, coefficient := (-20509707685811983393021231104) }, { argument := 670251885157254359249059840, coefficient := (-670251885157254359249059840) }, { argument := 21045909193937786880420478976, coefficient := (-21045909193937786880420478976) }, { argument := 670251885157254359249059840, coefficient := (-670251885157254359249059840) }, { argument := 20509707685811983393021231104, coefficient := (-20509707685811983393021231104) }, { argument := 21448060325032139495969914880, coefficient := (-21448060325032139495969914880) }, { argument := 877732900422428580940611584, coefficient := (-877732900422428580940611584) }, { argument := 23283169109852989816202854400, coefficient := (-23283169109852989816202854400) }, { argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 467092691821525355723206164480, coefficient := (-467092691821525355723206164480) }, { argument := 151472396170831024704244940800, coefficient := (-151472396170831024704244940800) }, { argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 467092580483895655839993692160, coefficient := (-467092580483895655839993692160) }, { argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 556421384414875485685720023040, coefficient := (-556421384414875485685720023040) }, { argument := 13805079144683333897095741440, coefficient := (-13805079144683333897095741440) }, { argument := 151472396170831024704244940800, coefficient := (-151472396170831024704244940800) }, { argument := 556421384414875485685720023040, coefficient := (-556421384414875485685720023040) }, { argument := 23283169109852989816202854400, coefficient := (-23283169109852989816202854400) }, { argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 13805079144683333897095741440, coefficient := (-13805079144683333897095741440) }] }

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
def constantNumerator : ℤ := (-410923992024560876670179298246656)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    363793325, 412835325, 29271263175, 759533775, 50445265325, 47149519725,
    6663794375, 47149519725, 49135992675, 29271263175, 1460641875, 17382185415,
    173734136955, 347468188995, 17382185415, 11948660025, 87052217425, 23897336125,
    353070825, 2572305025, 706142125, 5260375, 1043315625, 1043315625,
    5260375, 35954555, 1473064775, 30331544425, 1473064775, 35954555,
    568045275, 5677586175, 11355169575, 568045275, 9245457, 378788085,
    7799539995, 378788085, 9245457, 17836621635, 178276205895, 356552324655,
    17836621635, 353070825, 2572305025, 706142125, 568045275, 5677586175,
    11355169575, 568045275, 687558975, 5009225575, 1375118875, 35954555,
    1473064775, 30331544425, 1473064775, 35954555, 17382185415, 173734136955,
    347468188995, 17382185415, 687558975, 5009225575
  ]
def negativeCoefficients : Array ℕ := #[
    13421604723997685733287526400, 7615467584861706696995635200, 33747468781463992741448908800, 1751365645345436749057228800, 58159431198790605515993907200, 54359695222837209864968601600,
    7682831837215643465154560000, 54359695222837209864968601600, 56649942605212011767581900800, 33747468781463992741448908800, 1684005428216766104862720000, 20040295362016990815364055040,
    801207290318922463836446392320, 801207094518263336455624458240, 20040295362016990815364055040, 110206936752469486427386675200, 401457493971973528393823027200, 110207010885322232647647232000,
    6513007148668492199441203200, 23725326237846025006166835200, 6513011529770209705459712000, 6064799459796242661376000, 1202861020154832932044800000, 1202861020154832932044800000,
    6064799459796242661376000, 82905559296139265950351360, 13586624454210772033286963200, 139879559342081684846883635200, 13586624454210772033286963200, 82905559296139265950351360,
    654911613137810157364838400, 26183244781664132805112627200, 26183238382949782237111910400, 654911613137810157364838400, 85274289561743244977504256, 13974813724331079805666590720,
    143876118180426875842508881920, 13974813724331079805666590720, 85274289561743244977504256, 20564224652527238941255925760, 822153886144253770080536494080, 822153685224623162245313986560,
    20564224652527238941255925760, 6513007148668492199441203200, 23725326237846025006166835200, 6513011529770209705459712000, 654911613137810157364838400, 26183244781664132805112627200,
    26183238382949782237111910400, 654911613137810157364838400, 6341612223703531878403276800, 23100975547376392769162444800, 6341616489513098923737088000, 82905559296139265950351360,
    13586624454210772033286963200, 139879559342081684846883635200, 13586624454210772033286963200, 82905559296139265950351360, 20040295362016990815364055040, 801207290318922463836446392320,
    801207094518263336455624458240, 20040295362016990815364055040, 6341612223703531878403276800, 23100975547376392769162444800
  ]
def negativeScales : Array ℕ := #[
    28, 28, 34, 29, 35, 35,
    32, 35, 35, 34, 30, 34,
    37, 38, 34, 33, 36, 34,
    28, 31, 29, 22, 29, 29,
    22, 25, 30, 34, 30, 25,
    29, 32, 33, 29, 23, 28,
    32, 28, 23, 34, 37, 38,
    34, 28, 31, 29, 29, 32,
    33, 29, 29, 32, 30, 25,
    30, 34, 30, 25, 34, 37,
    38, 34, 29, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28438543831286392, 28620991181957953, 34768765954505907, 29500538879115002, 35553999816567726, 35456524024251474,
    32633696738085368, 35456524024251474, 35516061151229238, 34768765954505907, 30443955350748396, 34016890428561754,
    37338090300266936, 38338089947698159, 34016890428561754, 33476129786018619, 36341161996058522, 34476130756475345,
    28395382372134143, 31260414582174160, 29395383342590869, 22326734218909466, 29958528535608222, 29958528535608222,
    22326734218909466, 25099671218176001, 30456173725308212, 34820099908982713, 30456173725308212, 25099671218176001,
    29081430680756464, 32402630552461654, 33402630199892877, 29081430680756464, 23140313202673347, 28496815709805743,
    32860741894635460, 28496815709805743, 23140313202673347, 34054123334760729, 37375323206465913, 38375322853897136,
    34054123334760729, 28395382372134143, 31260414582174160, 29395383342590869, 29081430680756464, 32402630552461654,
    33402630199892877, 29081430680756464, 29356908224319502, 32221940434359524, 30356909194776229, 25099671218176001,
    30456173725308212, 34820099908982713, 30456173725308212, 25099671218176001, 34016890428561754, 37338090300266936,
    38338089947698159, 34016890428561754, 29356908224319502, 32221940434359524
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
noncomputable def negativeCeiling : ℝ := 147935983 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 7615467584861706696995635200, coefficient := (-7615467584861706696995635200) }, { argument := 33747468781463992741448908800, coefficient := (-33747468781463992741448908800) }, { argument := 1751365645345436749057228800, coefficient := (-1751365645345436749057228800) }, { argument := 58159431198790605515993907200, coefficient := (-58159431198790605515993907200) }, { argument := 54359695222837209864968601600, coefficient := (-54359695222837209864968601600) }, { argument := 7682831837215643465154560000, coefficient := (-7682831837215643465154560000) }, { argument := 54359695222837209864968601600, coefficient := (-54359695222837209864968601600) }, { argument := 56649942605212011767581900800, coefficient := (-56649942605212011767581900800) }, { argument := 33747468781463992741448908800, coefficient := (-33747468781463992741448908800) }, { argument := 1684005428216766104862720000, coefficient := (-1684005428216766104862720000) }, { argument := 20040295362016990815364055040, coefficient := (-20040295362016990815364055040) }, { argument := 801207290318922463836446392320, coefficient := (-801207290318922463836446392320) }, { argument := 801207094518263336455624458240, coefficient := (-801207094518263336455624458240) }, { argument := 20040295362016990815364055040, coefficient := (-20040295362016990815364055040) }, { argument := 110206936752469486427386675200, coefficient := (-110206936752469486427386675200) }, { argument := 401457493971973528393823027200, coefficient := (-401457493971973528393823027200) }, { argument := 110207010885322232647647232000, coefficient := (-110207010885322232647647232000) }, { argument := 6513007148668492199441203200, coefficient := (-6513007148668492199441203200) }, { argument := 23725326237846025006166835200, coefficient := (-23725326237846025006166835200) }, { argument := 6513011529770209705459712000, coefficient := (-6513011529770209705459712000) }, { argument := 6064799459796242661376000, coefficient := (-6064799459796242661376000) }, { argument := 1202861020154832932044800000, coefficient := (-1202861020154832932044800000) }, { argument := 1202861020154832932044800000, coefficient := (-1202861020154832932044800000) }, { argument := 6064799459796242661376000, coefficient := (-6064799459796242661376000) }, { argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }, { argument := 139879559342081684846883635200, coefficient := (-139879559342081684846883635200) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }, { argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 654911613137810157364838400, coefficient := (-654911613137810157364838400) }, { argument := 26183244781664132805112627200, coefficient := (-26183244781664132805112627200) }, { argument := 26183238382949782237111910400, coefficient := (-26183238382949782237111910400) }, { argument := 654911613137810157364838400, coefficient := (-654911613137810157364838400) }, { argument := 85274289561743244977504256, coefficient := (-85274289561743244977504256) }, { argument := 13974813724331079805666590720, coefficient := (-13974813724331079805666590720) }, { argument := 143876118180426875842508881920, coefficient := (-143876118180426875842508881920) }, { argument := 13974813724331079805666590720, coefficient := (-13974813724331079805666590720) }, { argument := 85274289561743244977504256, coefficient := (-85274289561743244977504256) }, { argument := 20564224652527238941255925760, coefficient := (-20564224652527238941255925760) }, { argument := 822153886144253770080536494080, coefficient := (-822153886144253770080536494080) }, { argument := 822153685224623162245313986560, coefficient := (-822153685224623162245313986560) }, { argument := 20564224652527238941255925760, coefficient := (-20564224652527238941255925760) }, { argument := 6513007148668492199441203200, coefficient := (-6513007148668492199441203200) }, { argument := 23725326237846025006166835200, coefficient := (-23725326237846025006166835200) }, { argument := 6513011529770209705459712000, coefficient := (-6513011529770209705459712000) }, { argument := 654911613137810157364838400, coefficient := (-654911613137810157364838400) }, { argument := 26183244781664132805112627200, coefficient := (-26183244781664132805112627200) }, { argument := 26183238382949782237111910400, coefficient := (-26183238382949782237111910400) }, { argument := 654911613137810157364838400, coefficient := (-654911613137810157364838400) }, { argument := 6341612223703531878403276800, coefficient := (-6341612223703531878403276800) }, { argument := 23100975547376392769162444800, coefficient := (-23100975547376392769162444800) }, { argument := 6341616489513098923737088000, coefficient := (-6341616489513098923737088000) }, { argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }, { argument := 139879559342081684846883635200, coefficient := (-139879559342081684846883635200) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }, { argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 20040295362016990815364055040, coefficient := (-20040295362016990815364055040) }, { argument := 801207290318922463836446392320, coefficient := (-801207290318922463836446392320) }, { argument := 801207094518263336455624458240, coefficient := (-801207094518263336455624458240) }, { argument := 20040295362016990815364055040, coefficient := (-20040295362016990815364055040) }, { argument := 6341612223703531878403276800, coefficient := (-6341612223703531878403276800) }, { argument := 23100975547376392769162444800, coefficient := (-23100975547376392769162444800) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
