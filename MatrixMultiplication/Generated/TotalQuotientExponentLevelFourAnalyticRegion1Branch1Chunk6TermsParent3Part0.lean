import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 6, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk6

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
def constantNumerator : ℤ := (-2410748853561935810544840560607232)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    12963489, 105, 197843115, 1185, 105, 98921553,
    105, 105, 4353, 27, 1185, 4353,
    12963525, 105, 27, 105, 564734755796519, 29418844749,
    763363237, 4204266999298063, 47387240943, 1129809861155747, 47387240943, 49383729409,
    29418844749, 1468006225, 1139270928086445, 10209529655, 1139271442393683, 10209529655,
    5497439045, 20421616075, 343517615, 121878071103, 121878100161, 12963489,
    3162504839, 3162505593, 105, 564735010695641, 29418851763, 763363419,
    4204268882266097, 47387252241, 1129810371011677, 47387252241, 49383741183, 29418851763,
    1468006575, 8486541645861541, 37925858425, 8486545446497627, 37925858425, 197843115,
    196318569621, 196318616427, 1185, 105, 2279244643000833, 637961285,
    2279245671734783, 637961285, 98921553, 105
  ]
def negativeCoefficients : Array ℕ := #[
    61218345954649334161650745344, 16247963015620616108051005440, 1868575390285049496044914606080, 183369868319146953219432775680, 16247963015620616108051005440, 1868575305282452804391300759552,
    16247963015620616108051005440, 16247963015620616108051005440, 673594123876157542079485968384, 16712190530352633711138177024, 183369868319146953219432775680, 673594123876157542079485968384,
    61218515959842717468878438400, 16247963015620616108051005440, 16712190530352633711138177024, 16247963015620616108051005440, 1271669617884185512191000051712, 135670475007249277877376516096,
    7040783134108744959704170496, 4733583822851207473698609037312, 218535076508682968556971753472, 1272052817425133503106282160128, 218535076508682968556971753472, 227742254453286711965815668736,
    135670475007249277877376516096, 6769983782796870153561702400, 1282705031801038211882082631680, 47083145164683293270076293120, 1282705610859509564569332744192, 47083145164683293270076293120,
    50704925561966623521620623360, 188356162653538982081173913600, 50694252229728714990781726720, 140515849114651037801568534528, 140515882616244118667327963136, 61218345954649334161650745344,
    7292239674612628708265033728, 7292241413218257655390273536, 16247963015620616108051005440, 1271670191865980940324299603968, 135670507353615011127075274752, 7040784812762455667273367552,
    4733585942884741541937469718528, 218535128611511604749600292864, 1272053391471877593265705320448, 218535128611511604749600292864, 227742308751277892929880850432, 135670507353615011127075274752,
    6769985396886976603147468800, 4777498224245778984358790561792, 174902151035429054789661491200, 4777500363813686569416339226624, 174902151035429054789661491200, 1868575390285049496044914606080,
    226339900669707360291149316096, 226339954633351304919228874752, 183369868319146953219432775680, 16247963015620616108051005440, 1283100665613093835342815952896, 47073234213319521062868746240,
    1283101244738823070765123895296, 47073234213319521062868746240, 1868575305282452804391300759552, 16247963015620616108051005440
  ]
def negativeScales : Array ℕ := #[
    23, 6, 27, 10, 6, 26,
    6, 6, 12, 4, 10, 12,
    23, 6, 4, 6, 49, 34,
    29, 51, 35, 50, 35, 35,
    34, 30, 50, 33, 50, 33,
    32, 34, 28, 36, 36, 23,
    31, 31, 6, 49, 34, 29,
    51, 35, 50, 35, 35, 34,
    30, 52, 35, 52, 35, 27,
    37, 37, 10, 6, 51, 29,
    51, 29, 26, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23627950722381991, 6714245517766967, 27559781619062854, 10210671343785622, 6714245517766967, 26559781553433804,
    6714245517766967, 6714245517766967, 12087794304787901, 4754887502413606, 10210671343785622, 12087794304787901,
    23627954728784077, 6714245517766967, 4754887502413606, 6714245517766967, 49004566751086864, 34776021543663192,
    29507794468216387, 51900775720809882, 35463779613352801, 50005001421217461, 35463779613352801, 35523316740330668,
    34776021543663192, 30451210939849717, 50017032296017044, 33249197352794605, 50017032947300524, 33249197352794605,
    32356112556711118, 34249377988014579, 28355808838991081, 36826647617441753, 36826647961407063, 23627950722381991,
    31558420541287716, 31558420885253018, 6714245517766967, 49004567402262681, 34776021887628496, 29507794812181688,
    51900776366950637, 35463779957318103, 50005002072270776, 35463779957318103, 35523317084295970, 34776021887628496,
    30451211283815019, 52914098189198053, 35142462784098067, 52914098835298476, 35142462784098067, 27559781619062854,
    37514405686423127, 37514406030388429, 10210671343785622, 6714245517766967, 51017477208072357, 29248893635074568,
    51017477859230642, 29248893635074568, 26559781553433804, 6714245517766967
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
noncomputable def negativeCeiling : ℝ := 11194770143 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 61218345954649334161650745344, coefficient := (-61218345954649334161650745344) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 1868575390285049496044914606080, coefficient := (-1868575390285049496044914606080) }, { argument := 183369868319146953219432775680, coefficient := (-183369868319146953219432775680) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 1868575305282452804391300759552, coefficient := (-1868575305282452804391300759552) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 673594123876157542079485968384, coefficient := (-673594123876157542079485968384) }, { argument := 16712190530352633711138177024, coefficient := (-16712190530352633711138177024) }, { argument := 183369868319146953219432775680, coefficient := (-183369868319146953219432775680) }, { argument := 673594123876157542079485968384, coefficient := (-673594123876157542079485968384) }, { argument := 61218515959842717468878438400, coefficient := (-61218515959842717468878438400) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 16712190530352633711138177024, coefficient := (-16712190530352633711138177024) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 1271669617884185512191000051712, coefficient := (-1271669617884185512191000051712) }, { argument := 135670475007249277877376516096, coefficient := (-135670475007249277877376516096) }, { argument := 7040783134108744959704170496, coefficient := (-7040783134108744959704170496) }, { argument := 4733583822851207473698609037312, coefficient := (-4733583822851207473698609037312) }, { argument := 218535076508682968556971753472, coefficient := (-218535076508682968556971753472) }, { argument := 1272052817425133503106282160128, coefficient := (-1272052817425133503106282160128) }, { argument := 218535076508682968556971753472, coefficient := (-218535076508682968556971753472) }, { argument := 227742254453286711965815668736, coefficient := (-227742254453286711965815668736) }, { argument := 135670475007249277877376516096, coefficient := (-135670475007249277877376516096) }, { argument := 6769983782796870153561702400, coefficient := (-6769983782796870153561702400) }, { argument := 1282705031801038211882082631680, coefficient := (-1282705031801038211882082631680) }, { argument := 47083145164683293270076293120, coefficient := (-47083145164683293270076293120) }, { argument := 1282705610859509564569332744192, coefficient := (-1282705610859509564569332744192) }, { argument := 47083145164683293270076293120, coefficient := (-47083145164683293270076293120) }, { argument := 50704925561966623521620623360, coefficient := (-50704925561966623521620623360) }, { argument := 188356162653538982081173913600, coefficient := (-188356162653538982081173913600) }, { argument := 50694252229728714990781726720, coefficient := (-50694252229728714990781726720) }, { argument := 140515849114651037801568534528, coefficient := (-140515849114651037801568534528) }, { argument := 140515882616244118667327963136, coefficient := (-140515882616244118667327963136) }, { argument := 61218345954649334161650745344, coefficient := (-61218345954649334161650745344) }, { argument := 7292239674612628708265033728, coefficient := (-7292239674612628708265033728) }, { argument := 7292241413218257655390273536, coefficient := (-7292241413218257655390273536) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 1271670191865980940324299603968, coefficient := (-1271670191865980940324299603968) }, { argument := 135670507353615011127075274752, coefficient := (-135670507353615011127075274752) }, { argument := 7040784812762455667273367552, coefficient := (-7040784812762455667273367552) }, { argument := 4733585942884741541937469718528, coefficient := (-4733585942884741541937469718528) }, { argument := 218535128611511604749600292864, coefficient := (-218535128611511604749600292864) }, { argument := 1272053391471877593265705320448, coefficient := (-1272053391471877593265705320448) }, { argument := 218535128611511604749600292864, coefficient := (-218535128611511604749600292864) }, { argument := 227742308751277892929880850432, coefficient := (-227742308751277892929880850432) }, { argument := 135670507353615011127075274752, coefficient := (-135670507353615011127075274752) }, { argument := 6769985396886976603147468800, coefficient := (-6769985396886976603147468800) }, { argument := 4777498224245778984358790561792, coefficient := (-4777498224245778984358790561792) }, { argument := 174902151035429054789661491200, coefficient := (-174902151035429054789661491200) }, { argument := 4777500363813686569416339226624, coefficient := (-4777500363813686569416339226624) }, { argument := 174902151035429054789661491200, coefficient := (-174902151035429054789661491200) }, { argument := 1868575390285049496044914606080, coefficient := (-1868575390285049496044914606080) }, { argument := 226339900669707360291149316096, coefficient := (-226339900669707360291149316096) }, { argument := 226339954633351304919228874752, coefficient := (-226339954633351304919228874752) }, { argument := 183369868319146953219432775680, coefficient := (-183369868319146953219432775680) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 1283100665613093835342815952896, coefficient := (-1283100665613093835342815952896) }, { argument := 47073234213319521062868746240, coefficient := (-47073234213319521062868746240) }, { argument := 1283101244738823070765123895296, coefficient := (-1283101244738823070765123895296) }, { argument := 47073234213319521062868746240, coefficient := (-47073234213319521062868746240) }, { argument := 1868575305282452804391300759552, coefficient := (-1868575305282452804391300759552) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }] }

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
def constantNumerator : ℤ := 5765946993367918809581516287377408
def positiveArguments : Array ℕ := #[
    9, 9, 13203, 14445, 13203, 14445,
    171, 28557, 741, 30723, 45999, 1425,
    45999, 47937, 28557, 1425, 93, 105,
    45, 1185, 105, 45, 105, 105,
    4353, 27, 1185, 4353, 93, 105,
    27, 105, 63, 424673187, 424673373, 1117631519,
    4056105303, 558859589
  ]
def positiveCoefficients : Array ℕ := #[
    45635421608216258453881315393536, 1426106925256758076683791106048, 510766323083902367796660535296, 558813870858666189716182794240, 510766323083902367796660535296, 558813870858666189716182794240,
    26460968339725003375968780288, 552372714091759445473348288512, 28666049034702086990632845312, 594269247296324034151965523968, 889750060423253238516950237184, 27563508687213545183300812800,
    889750060423253238516950237184, 927236432237863659966239342592, 552372714091759445473348288512, 27563508687213545183300812800, 28782105913385091391404638208, 32495926031241232216102010880,
    27853650883921056185230295040, 366739736638293906438865551360, 32495926031241232216102010880, 27853650883921056185230295040, 32495926031241232216102010880, 32495926031241232216102010880,
    1347188247752315084158971936768, 33424381060705267422276354048, 366739736638293906438865551360, 1347188247752315084158971936768, 28782105913385091391404638208, 32495926031241232216102010880,
    33424381060705267422276354048, 32495926031241232216102010880, 9982748476797306536786537742336, 16043699395697865107676610953216, 16043706422579191617708688932864, 5277865625524289059174140084224,
    19154415733877026609000913829888, 5278279583447810929403927461888
  ]
def positiveScales : Array ℕ := #[
    3, 3, 13, 13, 13, 13,
    7, 14, 9, 14, 15, 10,
    15, 15, 14, 10, 6, 6,
    5, 10, 6, 5, 6, 6,
    12, 4, 10, 12, 6, 6,
    4, 6, 5, 28, 28, 30,
    31, 29
  ]
def negativeArguments : Array ℕ := #[
    5497439045, 20421616075, 343517615, 196318569621, 196318616427, 105,
    204589736123, 204589784901, 4353, 27, 121878071103, 121878100161,
    1185, 4353, 12963525, 6081740075, 6081741525, 105,
    27, 105, 9, 27, 57, 3,
    63, 405
  ]
def negativeCoefficients : Array ℕ := #[
    50704925561966623521620623360, 188356162653538982081173913600, 50694252229728714990781726720, 226339900669707360291149316096, 226339954633351304919228874752, 16247963015620616108051005440,
    235875906398046951678880514048, 235875962635252103391662309376, 673594123876157542079485968384, 16712190530352633711138177024, 140515849114651037801568534528, 140515882616244118667327963136,
    183369868319146953219432775680, 673594123876157542079485968384, 61218515959842717468878438400, 7011768917896758373331763200, 7011770589632940053259878400, 16247963015620616108051005440,
    16712190530352633711138177024, 16247963015620616108051005440, 1426106925256758076683791106048, 2139160387885137115025686659072, 4516005263313067242832005169152, 3802951800684688204490109616128,
    9982748476797306536786537742336, 32087405818277056725385299886080
  ]
def negativeScales : Array ℕ := #[
    32, 34, 28, 37, 37, 6,
    37, 37, 12, 4, 36, 36,
    10, 12, 23, 32, 32, 6,
    4, 6, 3, 4, 5, 1,
    5, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 3169925001442312, 13688578157112273, 13818282583394157, 13688578157112273, 13818282583394157,
    7417852514885896, 14801556807318634, 9533329732305783, 14907031476611228, 15489314877442509, 10476746203939458,
    15489314877442509, 15548852004419805, 14801556807318634, 10476746203939458, 6539158811107971, 6714245517659862,
    5491853096329661, 10210671343785621, 6714245517659862, 5491853096329661, 6714245517659862, 6714245517659862,
    12087794304787900, 4754887502147955, 10210671343785621, 12087794304787900, 6539158811107971, 6714245517659862,
    4754887502147955, 6714245517659862, 5977279922488012, 28661777781831671, 28661778413708669, 30057797466732273,
    31917447961123443, 29057910616946084
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32356112556711118, 34249377988014579, 28355808838991081, 37514405686423127, 37514406030388429, 6714245517766967,
    37573942813402759, 37573943157368061, 12087794304787901, 4754887502413606, 36826647617441753, 36826647961407063,
    10210671343785622, 12087794304787901, 23627954728784077, 32501837012919924, 32501837356885226, 6714245517766967,
    4754887502413606, 6714245517766967, 3169925001442313, 4754887502413606, 5832890015409720, 1584962500724866,
    5977279939904027, 8661778097800657
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 2638455973 / 100000000000
noncomputable def negativeCeiling : ℝ := 2767297967 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 50704925561966623521620623360, coefficient := (-50704925561966623521620623360) }, { argument := 188356162653538982081173913600, coefficient := (-188356162653538982081173913600) }, { argument := 50694252229728714990781726720, coefficient := (-50694252229728714990781726720) }, { argument := 226339900669707360291149316096, coefficient := (-226339900669707360291149316096) }, { argument := 226339954633351304919228874752, coefficient := (-226339954633351304919228874752) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 235875906398046951678880514048, coefficient := (-235875906398046951678880514048) }, { argument := 235875962635252103391662309376, coefficient := (-235875962635252103391662309376) }, { argument := 673594123876157542079485968384, coefficient := (-673594123876157542079485968384) }, { argument := 16712190530352633711138177024, coefficient := (-16712190530352633711138177024) }, { argument := 140515849114651037801568534528, coefficient := (-140515849114651037801568534528) }, { argument := 140515882616244118667327963136, coefficient := (-140515882616244118667327963136) }, { argument := 183369868319146953219432775680, coefficient := (-183369868319146953219432775680) }, { argument := 673594123876157542079485968384, coefficient := (-673594123876157542079485968384) }, { argument := 61218515959842717468878438400, coefficient := (-61218515959842717468878438400) }, { argument := 7011768917896758373331763200, coefficient := (-7011768917896758373331763200) }, { argument := 7011770589632940053259878400, coefficient := (-7011770589632940053259878400) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 16712190530352633711138177024, coefficient := (-16712190530352633711138177024) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 45635421608216258453881315393536, coefficient := 45635421608216258453881315393536 }, { argument := 1426106925256758076683791106048, coefficient := 1426106925256758076683791106048 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 510766323083902367796660535296, coefficient := 510766323083902367796660535296 }, { argument := 558813870858666189716182794240, coefficient := 558813870858666189716182794240 }, { argument := 510766323083902367796660535296, coefficient := 510766323083902367796660535296 }, { argument := 558813870858666189716182794240, coefficient := 558813870858666189716182794240 }, { argument := 2139160387885137115025686659072, coefficient := (-2139160387885137115025686659072) }, { argument := 26460968339725003375968780288, coefficient := 26460968339725003375968780288 }, { argument := 552372714091759445473348288512, coefficient := 552372714091759445473348288512 }, { argument := 28666049034702086990632845312, coefficient := 28666049034702086990632845312 }, { argument := 594269247296324034151965523968, coefficient := 594269247296324034151965523968 }, { argument := 889750060423253238516950237184, coefficient := 889750060423253238516950237184 }, { argument := 27563508687213545183300812800, coefficient := 27563508687213545183300812800 }, { argument := 889750060423253238516950237184, coefficient := 889750060423253238516950237184 }, { argument := 927236432237863659966239342592, coefficient := 927236432237863659966239342592 }, { argument := 552372714091759445473348288512, coefficient := 552372714091759445473348288512 }, { argument := 27563508687213545183300812800, coefficient := 27563508687213545183300812800 }, { argument := 4516005263313067242832005169152, coefficient := (-4516005263313067242832005169152) }, { argument := 28782105913385091391404638208, coefficient := 28782105913385091391404638208 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 27853650883921056185230295040, coefficient := 27853650883921056185230295040 }, { argument := 366739736638293906438865551360, coefficient := 366739736638293906438865551360 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 27853650883921056185230295040, coefficient := 27853650883921056185230295040 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 1347188247752315084158971936768, coefficient := 1347188247752315084158971936768 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 366739736638293906438865551360, coefficient := 366739736638293906438865551360 }, { argument := 1347188247752315084158971936768, coefficient := 1347188247752315084158971936768 }, { argument := 28782105913385091391404638208, coefficient := 28782105913385091391404638208 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 3802951800684688204490109616128, coefficient := (-3802951800684688204490109616128) }, { argument := 9982748476797306536786537742336, coefficient := 9982748476797306536786537742336 }, { argument := 9982748476797306536786537742336, coefficient := (-9982748476797306536786537742336) }, { argument := 16043699395697865107676610953216, coefficient := 16043699395697865107676610953216 }, { argument := 16043706422579191617708688932864, coefficient := 16043706422579191617708688932864 }, { argument := 32087405818277056725385299886080, coefficient := (-32087405818277056725385299886080) }, { argument := 5277865625524289059174140084224, coefficient := 5277865625524289059174140084224 }, { argument := 19154415733877026609000913829888, coefficient := 19154415733877026609000913829888 }, { argument := 5278279583447810929403927461888, coefficient := 5278279583447810929403927461888 }] }

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

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3054051260302810545777929009233920)
def positiveArguments : Array ℕ := #[
    9916065, 196368555, 98184273, 9916101
  ]
def positiveCoefficients : Array ℕ := #[
    93654585995913576931896852480, 3709297129686177935904598917120, 3709296959680984552597371224064, 93654926006300343546352238592
  ]
def positiveScales : Array ℕ := #[
    23, 27, 26, 23
  ]
def negativeArguments : Array ℕ := #[
    375, 3
  ]
def negativeCoefficients : Array ℕ := #[
    29710560942849126597578981376000, 7605903601369376408980219232256
  ]
def negativeScales : Array ℕ := #[
    8, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    23241336297674011, 27548988684792068, 26548988618670200, 23241341535328987
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8550746785384604, 1584962500724866
  ]

abbrev PositiveTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 616955983 / 250000000000
noncomputable def negativeCeiling : ℝ := 3203093 / 1000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 29710560942849126597578981376000, coefficient := (-29710560942849126597578981376000) }, { argument := 93654585995913576931896852480, coefficient := 93654585995913576931896852480 }, { argument := 3709297129686177935904598917120, coefficient := 3709297129686177935904598917120 }, { argument := 3709296959680984552597371224064, coefficient := 3709296959680984552597371224064 }, { argument := 93654926006300343546352238592, coefficient := 93654926006300343546352238592 }, { argument := 7605903601369376408980219232256, coefficient := (-7605903601369376408980219232256) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk6
