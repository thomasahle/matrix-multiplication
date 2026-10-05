import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 1010598457306994278901299590201344
def positiveArguments : Array ℕ := #[
    187, 1, 96506545, 2545, 96472399, 1285,
    39201337, 665, 217, 1194056915, 2191, 313610597,
    4389, 1967, 665, 217, 4064255, 4653,
    29482237, 115137, 3663, 29482251, 1881, 1881,
    63657, 3465, 115137, 63657, 4064241, 3663,
    3465, 4653, 283699, 12452825, 1377, 70836195
  ]
def positiveCoefficients : Array ℕ := #[
    14815666390167431129992718712832, 316912650057057350374175801344, 911478546971102289899175280640, 196909837498830799976141946880, 911156047119254156088241553408, 198844118810214206655671828480,
    1480984639459821512740271292416, 823230126124777882807917608960, 33579123565615939956638744576, 5638774354034728911010361507840, 678081656518567045575995293696, 1480984171945539708645395136512,
    679164854052941753316532027392, 608757014318585750181644337152, 823230126124777882807917608960, 33579123565615939956638744576, 153543212718682959263920291840, 90002109418669912798525390848,
    2227614845581109124737617887232, 2227073473487512948610319777792, 70852724435974186671179563008, 2227615903391201287538145755136, 72767662934243759283914145792, 72767662934243759283914145792,
    1231305454387335189988336730112, 67022847439435041445710397440, 2227073473487512948610319777792, 1231305454387335189988336730112, 153542683813636877863656357888, 70852724435974186671179563008,
    67022847439435041445710397440, 90002109418669912798525390848, 2679461297647270954960683008, 117613606794082379316487782400, 53270107315499019954252939264, 669028946084036695876373053440
  ]
def positiveScales : Array ℕ := #[
    7, 0, 26, 11, 26, 10,
    25, 9, 7, 30, 11, 28,
    12, 10, 9, 7, 21, 12,
    24, 16, 11, 24, 10, 10,
    15, 11, 16, 15, 21, 11,
    11, 12, 18, 23, 10, 26
  ]
def negativeArguments : Array ℕ := #[
    18894755145, 5526286815, 226543635, 226441197, 35, 377572725,
    377401995, 15, 927627015, 25372956909, 7421013723, 5814619965,
    5811990723, 35, 6569765415, 6566794713, 395, 15,
    517165145, 31820135, 516960269, 16066355, 121181, 31,
    1, 7, 155, 155
  ]
def negativeCoefficients : Array ℕ := #[
    21784169530951363102003691520, 6371374909638780202191421440, 8357984912745739514617528320, 8354205617606894196520648704, 676998458984192337835458560, 435311714205507266386329600,
    435114875917025739402117120, 580284393415022003858964480, 8555849070782065671269253120, 29253027655848973308404957184, 8555846307229219128657051648, 13407600797529623804698951680,
    13401538178244392773585207296, 676998458984192337835458560, 7574423827175826435122135040, 7570998840956247865596837888, 7640411179964456384143032320, 580284393415022003858964480,
    596250817103618184335851520, 73372235841985985401323520, 596014611157440351954796544, 74092984720590955788369920, 1144522185521252953281789952, 599627206528856070654263296,
    316912650057057350374175801344, 2218388550399401452619230609408, 12280365189710972326999312302080, 12280365189710972326999312302080
  ]
def negativeScales : Array ℕ := #[
    34, 32, 27, 27, 5, 28,
    28, 3, 29, 34, 32, 32,
    32, 5, 32, 32, 8, 3,
    28, 24, 28, 23, 16, 4,
    0, 2, 7, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7546894459887560, 0, 26524123452383366, 11313449940963057, 26523612906886959, 10327552644081240,
    25224399523918756, 9377210530388551, 7761551232426566, 30153224458621894, 11097373768990222, 28224399068491586,
    12099676554859642, 10941781241718677, 9377210530388551, 7761551232426566, 21954559491333525, 12183945471757246,
    24813342658957298, 16812992001500797, 11838809985622091, 24813343344038480, 10877284133344468, 10877284133344468,
    15958031546671225, 11758639637007751, 16812992001500797, 15958031546671225, 21954554521722828, 11838809985622091,
    11758639637007751, 12183945471757246, 18114001539756226, 23569969727883581, 10427312844134962, 26077983383330410
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    34137266771870382, 32363663294138872, 27755213716620416, 27754561214428378, 5129283016944967, 28492179310534916,
    28491526808346416, 3906890600547867, 29788969595379464, 34562572606604990, 32788969129386593, 32437037756342276,
    32436385254153779, 5129283016944967, 32613194711504187, 32612542209315549, 8625708843075807, 3906890600547867,
    28946049815013747, 24923436627275891, 28945478175176391, 23937539332217928, 16886803993895011, 4954196321574415,
    0, 2807354922807594, 7276124405274238, 7276124405274238
  ]

abbrev PositiveTerm := Fin 36
abbrev NegativeTerm := Fin 28
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
noncomputable def positiveFloor : ℝ := 267566983 / 31250000000
noncomputable def negativeCeiling : ℝ := 1140036353 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 21784169530951363102003691520, coefficient := (-21784169530951363102003691520) }, { argument := 6371374909638780202191421440, coefficient := (-6371374909638780202191421440) }, { argument := 8357984912745739514617528320, coefficient := (-8357984912745739514617528320) }, { argument := 8354205617606894196520648704, coefficient := (-8354205617606894196520648704) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 435311714205507266386329600, coefficient := (-435311714205507266386329600) }, { argument := 435114875917025739402117120, coefficient := (-435114875917025739402117120) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 8555849070782065671269253120, coefficient := (-8555849070782065671269253120) }, { argument := 29253027655848973308404957184, coefficient := (-29253027655848973308404957184) }, { argument := 8555846307229219128657051648, coefficient := (-8555846307229219128657051648) }, { argument := 13407600797529623804698951680, coefficient := (-13407600797529623804698951680) }, { argument := 13401538178244392773585207296, coefficient := (-13401538178244392773585207296) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 7574423827175826435122135040, coefficient := (-7574423827175826435122135040) }, { argument := 7570998840956247865596837888, coefficient := (-7570998840956247865596837888) }, { argument := 7640411179964456384143032320, coefficient := (-7640411179964456384143032320) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 596250817103618184335851520, coefficient := (-596250817103618184335851520) }, { argument := 73372235841985985401323520, coefficient := (-73372235841985985401323520) }, { argument := 596014611157440351954796544, coefficient := (-596014611157440351954796544) }, { argument := 74092984720590955788369920, coefficient := (-74092984720590955788369920) }, { argument := 1144522185521252953281789952, coefficient := (-1144522185521252953281789952) }, { argument := 599627206528856070654263296, coefficient := (-599627206528856070654263296) }, { argument := 14815666390167431129992718712832, coefficient := 14815666390167431129992718712832 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 911478546971102289899175280640, coefficient := 911478546971102289899175280640 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 911156047119254156088241553408, coefficient := 911156047119254156088241553408 }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 2218388550399401452619230609408, coefficient := (-2218388550399401452619230609408) }, { argument := 1480984639459821512740271292416, coefficient := 1480984639459821512740271292416 }, { argument := 823230126124777882807917608960, coefficient := 823230126124777882807917608960 }, { argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 5638774354034728911010361507840, coefficient := 5638774354034728911010361507840 }, { argument := 678081656518567045575995293696, coefficient := 678081656518567045575995293696 }, { argument := 1480984171945539708645395136512, coefficient := 1480984171945539708645395136512 }, { argument := 679164854052941753316532027392, coefficient := 679164854052941753316532027392 }, { argument := 608757014318585750181644337152, coefficient := 608757014318585750181644337152 }, { argument := 823230126124777882807917608960, coefficient := 823230126124777882807917608960 }, { argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 12280365189710972326999312302080, coefficient := (-12280365189710972326999312302080) }, { argument := 153543212718682959263920291840, coefficient := 153543212718682959263920291840 }, { argument := 90002109418669912798525390848, coefficient := 90002109418669912798525390848 }, { argument := 2227614845581109124737617887232, coefficient := 2227614845581109124737617887232 }, { argument := 2227073473487512948610319777792, coefficient := 2227073473487512948610319777792 }, { argument := 70852724435974186671179563008, coefficient := 70852724435974186671179563008 }, { argument := 2227615903391201287538145755136, coefficient := 2227615903391201287538145755136 }, { argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 1231305454387335189988336730112, coefficient := 1231305454387335189988336730112 }, { argument := 67022847439435041445710397440, coefficient := 67022847439435041445710397440 }, { argument := 2227073473487512948610319777792, coefficient := 2227073473487512948610319777792 }, { argument := 1231305454387335189988336730112, coefficient := 1231305454387335189988336730112 }, { argument := 153542683813636877863656357888, coefficient := 153542683813636877863656357888 }, { argument := 70852724435974186671179563008, coefficient := 70852724435974186671179563008 }, { argument := 67022847439435041445710397440, coefficient := 67022847439435041445710397440 }, { argument := 90002109418669912798525390848, coefficient := 90002109418669912798525390848 }, { argument := 12280365189710972326999312302080, coefficient := (-12280365189710972326999312302080) }, { argument := 2679461297647270954960683008, coefficient := 2679461297647270954960683008 }, { argument := 117613606794082379316487782400, coefficient := 117613606794082379316487782400 }, { argument := 53270107315499019954252939264, coefficient := 53270107315499019954252939264 }, { argument := 669028946084036695876373053440, coefficient := 669028946084036695876373053440 }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-107400387801784108128602668662784)
def positiveArguments : Array ℕ := #[
    1413, 45, 1377, 783, 1413, 22059,
    27, 6226415, 1377, 45, 27, 45,
    693, 783, 283699, 242365, 8437059, 35,
    31, 1451, 395, 4218531, 1451, 35,
    35, 15, 35, 395, 15, 121181,
    31
  ]
def positiveCoefficients : Array ℕ := #[
    54662789859695072763514454016, 1740853180245066011576893440, 53270107315499019954252939264, 30290845336264148601437945856, 54662789859695072763514454016, 853366228956131358874993164288,
    33424381060705267422276354048, 117613654017747208012939919360, 53270107315499019954252939264, 1740853180245066011576893440, 33424381060705267422276354048, 1740853180245066011576893440,
    53618277951548033156568317952, 30290845336264148601437945856, 2679461297647270954960683008, 2289072705241403124434862080, 79685769271187371954041520128, 1353996917968384675670917120,
    1199254413057712141308526592, 56132843656346461839957164032, 15280822359928912768286064640, 79685797605386269171912802304, 56132843656346461839957164032, 1353996917968384675670917120,
    1353996917968384675670917120, 1160568786830044007717928960, 1353996917968384675670917120, 15280822359928912768286064640, 1160568786830044007717928960, 2289044371042505906563579904,
    1199254413057712141308526592
  ]
def positiveScales : Array ℕ := #[
    10, 5, 10, 9, 10, 14,
    4, 22, 10, 5, 4, 5,
    9, 9, 18, 17, 23, 5,
    4, 10, 8, 22, 10, 5,
    5, 3, 5, 8, 3, 16,
    4
  ]
def negativeArguments : Array ℕ := #[
    7, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2218388550399401452619230609408, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10464545750333933, 5491853096329661, 10427312844134962, 9612868497290540, 10464545750333933, 14429079770309150,
    4754887502147955, 22569970307147624, 10427312844134962, 5491853096329661, 4754887502147955, 5491853096329661,
    9436711542137211, 9612868497290540, 18114001539756226, 17886821848067009, 23008308759543552, 5129283016944966,
    4954196309696329, 10502831804066725, 8625708843063759, 22008309272528509, 10502831804066725, 5129283016944966,
    5129283016944966, 3906890595303263, 5129283016944966, 8625708843063759, 3906890595303263, 16886803990241446,
    4954196309696329
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 0
  ]

abbrev PositiveTerm := Fin 31
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 143628961 / 500000000000
noncomputable def negativeCeiling : ℝ := 14992893 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 54662789859695072763514454016, coefficient := 54662789859695072763514454016 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 53270107315499019954252939264, coefficient := 53270107315499019954252939264 }, { argument := 30290845336264148601437945856, coefficient := 30290845336264148601437945856 }, { argument := 54662789859695072763514454016, coefficient := 54662789859695072763514454016 }, { argument := 853366228956131358874993164288, coefficient := 853366228956131358874993164288 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 117613654017747208012939919360, coefficient := 117613654017747208012939919360 }, { argument := 53270107315499019954252939264, coefficient := 53270107315499019954252939264 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 53618277951548033156568317952, coefficient := 53618277951548033156568317952 }, { argument := 30290845336264148601437945856, coefficient := 30290845336264148601437945856 }, { argument := 2679461297647270954960683008, coefficient := 2679461297647270954960683008 }, { argument := 2218388550399401452619230609408, coefficient := (-2218388550399401452619230609408) }, { argument := 2289072705241403124434862080, coefficient := 2289072705241403124434862080 }, { argument := 79685769271187371954041520128, coefficient := 79685769271187371954041520128 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 56132843656346461839957164032, coefficient := 56132843656346461839957164032 }, { argument := 15280822359928912768286064640, coefficient := 15280822359928912768286064640 }, { argument := 79685797605386269171912802304, coefficient := 79685797605386269171912802304 }, { argument := 56132843656346461839957164032, coefficient := 56132843656346461839957164032 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 15280822359928912768286064640, coefficient := 15280822359928912768286064640 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 2289044371042505906563579904, coefficient := 2289044371042505906563579904 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2
