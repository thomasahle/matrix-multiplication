import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

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
def constantNumerator : ℤ := (-36785534417620617722026148761698304)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7813244158312915, 1604386504665, 52430931525, 1646331249885, 52430931525, 1604386504665,
    52430931525, 410986591894511, 23577942159617007, 20469443995, 55421790458140671, 231012296515,
    20469443995, 443374350459104515, 20469443995, 20469443995, 848604663907, 5263571313,
    231012296515, 848604663907, 23578104029133339, 20469443995, 5263571313, 20469443995,
    18043713, 8530604127, 323814930813, 34122439911, 18043713, 48173147325,
    1885254196035, 1885254196035, 48173147325, 1082992972223483, 2739285135, 71079255,
    7826380673445245, 4412381445, 2166413505112717, 4412381445, 4598281035, 2739285135,
    136690875, 4268506725, 167047840155, 167047840155, 4268506725, 27014518223,
    100352203105, 1688051981, 189558732443861, 1605, 189558785748779, 1605,
    27993366963169, 270355537199321, 13582108617, 9903745541863325, 529173063, 881955105,
    26987826213, 881955105, 529173063, 432334392471
  ]
def negativeCoefficients : Array ℕ := #[
    17593861739966374325480503377920, 3699463405858583829702330286080, 120897496923483131689618636800, 3796181403397370335054025195520, 120897496923483131689618636800, 3699463405858583829702330286080,
    3868719901551460214067796377600, 231364882763798731412243218432, 6636600720263391277901615726592, 377594594706895818700273745920, 249597554855488036706709003042816, 4261424711692109953903089418240,
    377594594706895818700273745920, 249597569939157349481964036423680, 377594594706895818700273745920, 377594594706895818700273745920, 15653993054848738083831348723712, 388383011698521413520281567232,
    4261424711692109953903089418240, 15653993054848738083831348723712, 6636646282481730992752646160384, 377594594706895818700273745920, 388383011698521413520281567232, 377594594706895818700273745920,
    332847755850465994717790208, 39340467781224873303692279808, 373333197247086014299518271488, 39340494763046845617732059136, 332847755850465994717790208, 111079714991172611157157478400,
    4347100208518087688990301880320, 4347100208518087688990301880320, 111079714991172611157157478400, 4877366746150543963677752557568, 25265445915130959524612014080, 1311180825934940015249326080,
    17623442542293828460456192245760, 40697035635749868934854082560, 4878329527178021206073400098816, 40697035635749868934854082560, 42411656715818636647103201280, 25265445915130959524612014080,
    1260750794168211553124352000, 9842506391622889596203827200, 385186094425653339530786242560, 385186094425653339530786242560, 9842506391622889596203827200, 996659807868487874679182196736,
    3702342815821712029094625935360, 996450012052013395968337641472, 106712079599874493771920965632, 242540742560184978175426560, 106712109607875598998776578048, 242540742560184978175426560,
    63035458512086730812174630912, 4870292386353649301453866532864, 1002182726556496736635519500288, 44602504731907881463257969459200, 624737284087166796863700467712, 32538400212873270669984399360,
    995675046513922082501522620416, 1041228806811944661439500779520, 624737284087166796863700467712, 15950323784350477282426352566272
  ]
def negativeScales : Array ℕ := #[
    52, 40, 35, 40, 35, 40,
    35, 48, 54, 34, 55, 37,
    34, 58, 34, 34, 39, 32,
    37, 39, 54, 34, 32, 34,
    24, 32, 38, 34, 24, 35,
    40, 40, 35, 49, 31, 26,
    52, 32, 50, 32, 32, 31,
    27, 31, 37, 37, 31, 34,
    36, 30, 47, 10, 47, 10,
    44, 47, 33, 53, 28, 29,
    34, 29, 28, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    52794843121978486, 40545158874702162, 35609699126903104, 40582391780903437, 35609699126903104, 40545158874702162,
    35609699126903104, 48546084656338922, 54388287326181760, 34252752864300393, 55621302837532366, 37749178690640770,
    34252752864300393, 58621302924717251, 34252752864300393, 34252752864300393, 39626301651433692, 32293394848797739,
    37749178690640770, 39626301651433692, 54388297230674073, 34252752864300393, 32293394848797739, 34252752864300393,
    24104992908320387, 32990000789223410, 38236378552296014, 34990001778701733, 24104992908320387, 35487510132334471,
    40777896199757704, 40777896199757704, 35487510132334471, 49943945313733267, 31351152299452756, 26082925224398639,
    52797266708238178, 32038910369535327, 50944230070372286, 32038910369535327, 32098447496512691, 31351152299452756,
    27026341696032271, 31991084326739097, 37281470373229352, 37281470373229352, 31991084326739097, 34653015902063654,
    36546281333345303, 30652712184343441, 47429638247412609, 10648357582030099, 47429638653106027, 10648357582030099,
    44670150254205719, 47941851242314541, 33660988423707874, 53136895670999942, 28979164400623197, 29716129977977535,
    34651589725699699, 29716129977977535, 28979164400623197, 38653356651874903
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
noncomputable def negativeCeiling : ℝ := 455588709597 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17593861739966374325480503377920, coefficient := (-17593861739966374325480503377920) }, { argument := 3699463405858583829702330286080, coefficient := (-3699463405858583829702330286080) }, { argument := 120897496923483131689618636800, coefficient := (-120897496923483131689618636800) }, { argument := 3796181403397370335054025195520, coefficient := (-3796181403397370335054025195520) }, { argument := 120897496923483131689618636800, coefficient := (-120897496923483131689618636800) }, { argument := 3699463405858583829702330286080, coefficient := (-3699463405858583829702330286080) }, { argument := 3868719901551460214067796377600, coefficient := (-3868719901551460214067796377600) }, { argument := 231364882763798731412243218432, coefficient := (-231364882763798731412243218432) }, { argument := 6636600720263391277901615726592, coefficient := (-6636600720263391277901615726592) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 249597554855488036706709003042816, coefficient := (-249597554855488036706709003042816) }, { argument := 4261424711692109953903089418240, coefficient := (-4261424711692109953903089418240) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 249597569939157349481964036423680, coefficient := (-249597569939157349481964036423680) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 15653993054848738083831348723712, coefficient := (-15653993054848738083831348723712) }, { argument := 388383011698521413520281567232, coefficient := (-388383011698521413520281567232) }, { argument := 4261424711692109953903089418240, coefficient := (-4261424711692109953903089418240) }, { argument := 15653993054848738083831348723712, coefficient := (-15653993054848738083831348723712) }, { argument := 6636646282481730992752646160384, coefficient := (-6636646282481730992752646160384) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 388383011698521413520281567232, coefficient := (-388383011698521413520281567232) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 332847755850465994717790208, coefficient := (-332847755850465994717790208) }, { argument := 39340467781224873303692279808, coefficient := (-39340467781224873303692279808) }, { argument := 373333197247086014299518271488, coefficient := (-373333197247086014299518271488) }, { argument := 39340494763046845617732059136, coefficient := (-39340494763046845617732059136) }, { argument := 332847755850465994717790208, coefficient := (-332847755850465994717790208) }, { argument := 111079714991172611157157478400, coefficient := (-111079714991172611157157478400) }, { argument := 4347100208518087688990301880320, coefficient := (-4347100208518087688990301880320) }, { argument := 4347100208518087688990301880320, coefficient := (-4347100208518087688990301880320) }, { argument := 111079714991172611157157478400, coefficient := (-111079714991172611157157478400) }, { argument := 4877366746150543963677752557568, coefficient := (-4877366746150543963677752557568) }, { argument := 25265445915130959524612014080, coefficient := (-25265445915130959524612014080) }, { argument := 1311180825934940015249326080, coefficient := (-1311180825934940015249326080) }, { argument := 17623442542293828460456192245760, coefficient := (-17623442542293828460456192245760) }, { argument := 40697035635749868934854082560, coefficient := (-40697035635749868934854082560) }, { argument := 4878329527178021206073400098816, coefficient := (-4878329527178021206073400098816) }, { argument := 40697035635749868934854082560, coefficient := (-40697035635749868934854082560) }, { argument := 42411656715818636647103201280, coefficient := (-42411656715818636647103201280) }, { argument := 25265445915130959524612014080, coefficient := (-25265445915130959524612014080) }, { argument := 1260750794168211553124352000, coefficient := (-1260750794168211553124352000) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 996659807868487874679182196736, coefficient := (-996659807868487874679182196736) }, { argument := 3702342815821712029094625935360, coefficient := (-3702342815821712029094625935360) }, { argument := 996450012052013395968337641472, coefficient := (-996450012052013395968337641472) }, { argument := 106712079599874493771920965632, coefficient := (-106712079599874493771920965632) }, { argument := 242540742560184978175426560, coefficient := (-242540742560184978175426560) }, { argument := 106712109607875598998776578048, coefficient := (-106712109607875598998776578048) }, { argument := 242540742560184978175426560, coefficient := (-242540742560184978175426560) }, { argument := 63035458512086730812174630912, coefficient := (-63035458512086730812174630912) }, { argument := 4870292386353649301453866532864, coefficient := (-4870292386353649301453866532864) }, { argument := 1002182726556496736635519500288, coefficient := (-1002182726556496736635519500288) }, { argument := 44602504731907881463257969459200, coefficient := (-44602504731907881463257969459200) }, { argument := 624737284087166796863700467712, coefficient := (-624737284087166796863700467712) }, { argument := 32538400212873270669984399360, coefficient := (-32538400212873270669984399360) }, { argument := 995675046513922082501522620416, coefficient := (-995675046513922082501522620416) }, { argument := 1041228806811944661439500779520, coefficient := (-1041228806811944661439500779520) }, { argument := 624737284087166796863700467712, coefficient := (-624737284087166796863700467712) }, { argument := 15950323784350477282426352566272, coefficient := (-15950323784350477282426352566272) }] }

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
def constantNumerator : ℤ := (-43184704717277553557996359749992448)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    27693390297, 540711328702607, 26987826213, 881955105, 27693390297, 881955105,
    26987826213, 881955105, 27993366963169, 5894485867109505, 20469443995, 443374350990946553,
    231012296515, 20469443995, 27710898611555379, 20469443995, 20469443995, 848604663907,
    5263571313, 231012296515, 848604663907, 11789052668957397, 20469443995, 5263571313,
    20469443995, 155118735487699, 103981079565, 2698111845, 71478579057742067, 167490481455,
    19860120942998925, 167490481455, 174547081665, 103981079565, 5188676625, 4268506725,
    167047840155, 167047840155, 4268506725, 1052513697, 3909826095, 65768259,
    3977247366876971, 4815, 3977249951019221, 4815, 1754189495, 6516376825,
    109613765, 32665850067, 10165, 32665857837, 10165, 93,
    1605, 4815, 10165, 26215, 21935, 613645,
    18725, 21935, 19795, 10165
  ]
def negativeCoefficients : Array ℕ := #[
    1021705766684220699037510139904, 4870294676920133327133180166144, 995675046513922082501522620416, 32538400212873270669984399360, 1021705766684220699037510139904, 32538400212873270669984399360,
    995675046513922082501522620416, 1041228806811944661439500779520, 63035458512086730812174630912, 6636601088663755430493809541120, 377594594706895818700273745920, 249597570238557800001559683137536,
    4261424711692109953903089418240, 377594594706895818700273745920, 249597585322204799692460909395968, 377594594706895818700273745920, 377594594706895818700273745920, 15653993054848738083831348723712,
    388383011698521413520281567232, 4261424711692109953903089418240, 15653993054848738083831348723712, 6636646650870960558216119844864, 377594594706895818700273745920, 388383011698521413520281567232,
    377594594706895818700273745920, 44709931477797360032737505837056, 239764045405448138910471290880, 12442844671739823576192122880, 160955451004709856014993106927616, 386206755772847600999501660160,
    44721016639211471130149152358400, 386206755772847600999501660160, 402478168035891985676060590080, 239764045405448138910471290880, 11964273722826753438646272000, 9842506391622889596203827200,
    385186094425653339530786242560, 385186094425653339530786242560, 9842506391622889596203827200, 621294425684252181618191499264, 2307953963109638667487559024640, 621163643876579779304937750528,
    2238991219928426623866033405952, 181905556920138733631569920, 2238992674671185895410423037952, 181905556920138733631569920, 32359084671054801125947473920, 120205935578627013931643699200,
    32352273118571863505465507840, 75322322017014626199256694784, 192011421193479774388879360, 75322339933414807789658701824, 192011421193479774388879360, 1798881619586568211962789888,
    242540742560184978175426560, 181905556920138733631569920, 192011421193479774388879360, 247593674696855498554081280, 3314723481655861368397496320, 5795713160761086874316963840,
    176852624783468213252915200, 3314723481655861368397496320, 186958489056809254010224640, 192011421193479774388879360
  ]
def negativeScales : Array ℕ := #[
    34, 48, 34, 29, 34, 29,
    34, 29, 44, 52, 34, 58,
    37, 34, 54, 34, 34, 39,
    32, 37, 39, 53, 34, 32,
    34, 47, 36, 31, 55, 37,
    54, 37, 37, 36, 32, 31,
    37, 37, 31, 29, 31, 25,
    51, 12, 51, 12, 30, 32,
    26, 34, 13, 34, 13, 6,
    10, 12, 13, 14, 14, 19,
    14, 14, 14, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34688822631932016, 48941851920834100, 34651589725699699, 29716129977977535, 34688822631932016, 29716129977977535,
    34651589725699699, 29716129977977535, 44670150254205719, 52388287406266338, 34252752864300393, 58621302926447811,
    37749178690640770, 34252752864300393, 54621303013632562, 34252752864300393, 34252752864300393, 39626301651433692,
    32293394848797739, 37749178690640770, 39626301651433692, 53388297310755680, 34252752864300393, 32293394848797739,
    34252752864300393, 47140366276323754, 36597530082699669, 31329303007640273, 55988360492774324, 37285288152776961,
    54140723926730424, 37285288152776961, 37344825279754325, 36597530082699669, 32272719479273905, 31991084326739097,
    37281470373229352, 37281470373229352, 31991084326739097, 29971191876910660, 31864457295647178, 25970888159116519,
    51820691718358606, 12233320082730822, 51820692655722497, 12233320082730822, 30708157456320712, 32601422887542458,
    26707853738600059, 34927064139552001, 13311322594732096, 34927064482715901, 13311322594732096, 6539158811108986,
    10648357582030099, 12233320082730822, 13311322594732096, 14678104925446590, 14420947085906609, 19227044757304335,
    14192678098233476, 14420947085906609, 14272848446917460, 13311322594732096
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
noncomputable def negativeCeiling : ℝ := 271012625879 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1021705766684220699037510139904, coefficient := (-1021705766684220699037510139904) }, { argument := 4870294676920133327133180166144, coefficient := (-4870294676920133327133180166144) }, { argument := 995675046513922082501522620416, coefficient := (-995675046513922082501522620416) }, { argument := 32538400212873270669984399360, coefficient := (-32538400212873270669984399360) }, { argument := 1021705766684220699037510139904, coefficient := (-1021705766684220699037510139904) }, { argument := 32538400212873270669984399360, coefficient := (-32538400212873270669984399360) }, { argument := 995675046513922082501522620416, coefficient := (-995675046513922082501522620416) }, { argument := 1041228806811944661439500779520, coefficient := (-1041228806811944661439500779520) }, { argument := 63035458512086730812174630912, coefficient := (-63035458512086730812174630912) }, { argument := 6636601088663755430493809541120, coefficient := (-6636601088663755430493809541120) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 249597570238557800001559683137536, coefficient := (-249597570238557800001559683137536) }, { argument := 4261424711692109953903089418240, coefficient := (-4261424711692109953903089418240) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 249597585322204799692460909395968, coefficient := (-249597585322204799692460909395968) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 15653993054848738083831348723712, coefficient := (-15653993054848738083831348723712) }, { argument := 388383011698521413520281567232, coefficient := (-388383011698521413520281567232) }, { argument := 4261424711692109953903089418240, coefficient := (-4261424711692109953903089418240) }, { argument := 15653993054848738083831348723712, coefficient := (-15653993054848738083831348723712) }, { argument := 6636646650870960558216119844864, coefficient := (-6636646650870960558216119844864) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 388383011698521413520281567232, coefficient := (-388383011698521413520281567232) }, { argument := 377594594706895818700273745920, coefficient := (-377594594706895818700273745920) }, { argument := 44709931477797360032737505837056, coefficient := (-44709931477797360032737505837056) }, { argument := 239764045405448138910471290880, coefficient := (-239764045405448138910471290880) }, { argument := 12442844671739823576192122880, coefficient := (-12442844671739823576192122880) }, { argument := 160955451004709856014993106927616, coefficient := (-160955451004709856014993106927616) }, { argument := 386206755772847600999501660160, coefficient := (-386206755772847600999501660160) }, { argument := 44721016639211471130149152358400, coefficient := (-44721016639211471130149152358400) }, { argument := 386206755772847600999501660160, coefficient := (-386206755772847600999501660160) }, { argument := 402478168035891985676060590080, coefficient := (-402478168035891985676060590080) }, { argument := 239764045405448138910471290880, coefficient := (-239764045405448138910471290880) }, { argument := 11964273722826753438646272000, coefficient := (-11964273722826753438646272000) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 621294425684252181618191499264, coefficient := (-621294425684252181618191499264) }, { argument := 2307953963109638667487559024640, coefficient := (-2307953963109638667487559024640) }, { argument := 621163643876579779304937750528, coefficient := (-621163643876579779304937750528) }, { argument := 2238991219928426623866033405952, coefficient := (-2238991219928426623866033405952) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 2238992674671185895410423037952, coefficient := (-2238992674671185895410423037952) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 32359084671054801125947473920, coefficient := (-32359084671054801125947473920) }, { argument := 120205935578627013931643699200, coefficient := (-120205935578627013931643699200) }, { argument := 32352273118571863505465507840, coefficient := (-32352273118571863505465507840) }, { argument := 75322322017014626199256694784, coefficient := (-75322322017014626199256694784) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 75322339933414807789658701824, coefficient := (-75322339933414807789658701824) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 242540742560184978175426560, coefficient := (-242540742560184978175426560) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 247593674696855498554081280, coefficient := (-247593674696855498554081280) }, { argument := 3314723481655861368397496320, coefficient := (-3314723481655861368397496320) }, { argument := 5795713160761086874316963840, coefficient := (-5795713160761086874316963840) }, { argument := 176852624783468213252915200, coefficient := (-176852624783468213252915200) }, { argument := 3314723481655861368397496320, coefficient := (-3314723481655861368397496320) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
