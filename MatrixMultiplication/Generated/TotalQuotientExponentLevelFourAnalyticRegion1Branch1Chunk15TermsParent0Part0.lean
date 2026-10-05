import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 15, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-112265425713537048725210870688251904)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    527499591, 73, 20688313769, 807, 143, 2586039713,
    143, 71, 5751, 145, 807, 5751,
    65938049, 71, 145, 73, 270113591438123277, 501,
    13, 987217204078091275, 807, 33764161506973789, 807, 841,
    501, 25, 270410548902599853, 270410575599919955, 501, 501,
    525222667, 13, 13, 105, 270113618208710387, 501,
    13, 987217304700150773, 807, 33764164851525539, 807, 841,
    501, 25, 988312139831473337, 988312240197438279, 10303213069, 807,
    807, 1185, 105, 135205124449761101, 135205137791322291, 20606430013,
    105, 807, 807, 105, 841, 841,
    4353, 27, 501, 501
  ]
def negativeCoefficients : Array ℕ := #[
    2491046388265846356539747598336, 2824050714619773752113627136, 97697799529816183706651904180224, 31219300365728183807612289024, 2766022275278271551727730688, 97697818112328293798705820073984,
    2766022275278271551727730688, 2746679462164437484932431872, 111240518217659718139763490816, 2804707901505939685318328320, 31219300365728183807612289024, 111240518217659718139763490816,
    2491069060347330613706418552832, 2746679462164437484932431872, 2804707901505939685318328320, 2824050714619773752113627136, 76030216859277399315667287539712, 4845374685015433732222353408,
    251456570479842868338884608, 277876939526239673137754433126400, 7804825091432045951903072256, 76030132590642200410432231964672, 7804825091432045951903072256, 8133652914367225087423152128,
    4845374685015433732222353408, 241785163922925834941235200, 76113802954674999001704529133568, 76113810469302552949082795540480, 4845374685015433732222353408, 4845374685015433732222353408,
    2480293918684204872481198047232, 251456570479842868338884608, 251456570479842868338884608, 2030995376952577013506375680, 76030224394527782633505000783872, 4845374685015433732222353408,
    251456570479842868338884608, 277876967848831526915546795737088, 7804825091432045951903072256, 76030140121903207921102379548672, 7804825091432045951903072256, 8133652914367225087423152128,
    4845374685015433732222353408, 241785163922925834941235200, 278185136541922553620790427779072, 278185164792430198212757001601024, 97311096125820186378291849986048, 7804825091432045951903072256,
    7804825091432045951903072256, 22921233539893369152429096960, 2030995376952577013506375680, 76113718511315704061356001984512, 76113726021946954539439900065792, 97311114424990307498167053058048,
    2030995376952577013506375680, 7804825091432045951903072256, 7804825091432045951903072256, 2030995376952577013506375680, 8133652914367225087423152128, 8133652914367225087423152128,
    84199265484519692759935746048, 2089023816294079213892272128, 4845374685015433732222353408, 4845374685015433732222353408
  ]
def negativeScales : Array ℕ := #[
    28, 6, 34, 9, 7, 31,
    7, 6, 12, 7, 9, 12,
    25, 6, 7, 6, 57, 8,
    3, 59, 9, 54, 9, 9,
    8, 4, 57, 57, 8, 8,
    28, 3, 3, 6, 57, 8,
    3, 59, 9, 54, 9, 9,
    8, 4, 59, 59, 33, 9,
    9, 10, 6, 56, 56, 34,
    6, 9, 9, 6, 9, 9,
    12, 4, 8, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28974594750014821, 6189824558880018, 34268097009913022, 9656424863302849, 7159871336778390, 31268097284319362,
    7159871336778390, 6149747119504683, 12489597122389498, 7179909090014935, 9656424863302849, 12489597122389498,
    25974607880544729, 6149747119504683, 7179909090014935, 6189824558880018, 57906343852444292, 8968666807433246,
    3700439718214233, 59776145149803949, 9656424863302849, 54906342253421889, 9656424863302849, 9715961990360049,
    8968666807433246, 4643856189792934, 57907929051366074, 57907929193801689, 8968666807433246, 8968666807433246,
    28968353953132604, 3700439718214233, 3700439718214233, 6714245517766967, 57906343995427822, 8968666807433246,
    3700439718214233, 59776145296850556, 9656424863302849, 54906342396329878, 9656424863302849, 9715961990360049,
    8968666807433246, 4643856189792934, 59777744375410433, 59777744521920294, 33262375262577989, 9656424863302849,
    9656424863302849, 10210671343785622, 6714245517766967, 56907927450787868, 56907927593147894, 34262375533874075,
    6714245517766967, 9656424863302849, 9656424863302849, 6714245517766967, 9715961990360049, 9715961990360049,
    12087794304787901, 4754887502413606, 8968666807433246, 8968666807433246
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
noncomputable def negativeCeiling : ℝ := 1375840553549 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2491046388265846356539747598336, coefficient := (-2491046388265846356539747598336) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 97697799529816183706651904180224, coefficient := (-97697799529816183706651904180224) }, { argument := 31219300365728183807612289024, coefficient := (-31219300365728183807612289024) }, { argument := 2766022275278271551727730688, coefficient := (-2766022275278271551727730688) }, { argument := 97697818112328293798705820073984, coefficient := (-97697818112328293798705820073984) }, { argument := 2766022275278271551727730688, coefficient := (-2766022275278271551727730688) }, { argument := 2746679462164437484932431872, coefficient := (-2746679462164437484932431872) }, { argument := 111240518217659718139763490816, coefficient := (-111240518217659718139763490816) }, { argument := 2804707901505939685318328320, coefficient := (-2804707901505939685318328320) }, { argument := 31219300365728183807612289024, coefficient := (-31219300365728183807612289024) }, { argument := 111240518217659718139763490816, coefficient := (-111240518217659718139763490816) }, { argument := 2491069060347330613706418552832, coefficient := (-2491069060347330613706418552832) }, { argument := 2746679462164437484932431872, coefficient := (-2746679462164437484932431872) }, { argument := 2804707901505939685318328320, coefficient := (-2804707901505939685318328320) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 76030216859277399315667287539712, coefficient := (-76030216859277399315667287539712) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 251456570479842868338884608, coefficient := (-251456570479842868338884608) }, { argument := 277876939526239673137754433126400, coefficient := (-277876939526239673137754433126400) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 76030132590642200410432231964672, coefficient := (-76030132590642200410432231964672) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 8133652914367225087423152128, coefficient := (-8133652914367225087423152128) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 241785163922925834941235200, coefficient := (-241785163922925834941235200) }, { argument := 76113802954674999001704529133568, coefficient := (-76113802954674999001704529133568) }, { argument := 76113810469302552949082795540480, coefficient := (-76113810469302552949082795540480) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 2480293918684204872481198047232, coefficient := (-2480293918684204872481198047232) }, { argument := 251456570479842868338884608, coefficient := (-251456570479842868338884608) }, { argument := 251456570479842868338884608, coefficient := (-251456570479842868338884608) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 76030224394527782633505000783872, coefficient := (-76030224394527782633505000783872) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 251456570479842868338884608, coefficient := (-251456570479842868338884608) }, { argument := 277876967848831526915546795737088, coefficient := (-277876967848831526915546795737088) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 76030140121903207921102379548672, coefficient := (-76030140121903207921102379548672) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 8133652914367225087423152128, coefficient := (-8133652914367225087423152128) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 241785163922925834941235200, coefficient := (-241785163922925834941235200) }, { argument := 278185136541922553620790427779072, coefficient := (-278185136541922553620790427779072) }, { argument := 278185164792430198212757001601024, coefficient := (-278185164792430198212757001601024) }, { argument := 97311096125820186378291849986048, coefficient := (-97311096125820186378291849986048) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 22921233539893369152429096960, coefficient := (-22921233539893369152429096960) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 76113718511315704061356001984512, coefficient := (-76113718511315704061356001984512) }, { argument := 76113726021946954539439900065792, coefficient := (-76113726021946954539439900065792) }, { argument := 97311114424990307498167053058048, coefficient := (-97311114424990307498167053058048) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 8133652914367225087423152128, coefficient := (-8133652914367225087423152128) }, { argument := 8133652914367225087423152128, coefficient := (-8133652914367225087423152128) }, { argument := 84199265484519692759935746048, coefficient := (-84199265484519692759935746048) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 121823839776655294895148352294354944
def positiveArguments : Array ℕ := #[
    26775, 3, 501, 13, 539, 807,
    25, 807, 841, 501, 25, 93,
    105, 45, 1185, 105, 45, 105,
    105, 4353, 27, 1185, 4353, 93,
    105, 27, 105, 9, 41, 1,
    429, 19, 1, 19, 37, 699,
    37, 429, 699, 9, 37, 37,
    41, 5055, 22775069573, 22775071867, 32217652667, 117748523033,
    8054403211, 525906473
  ]
def positiveCoefficients : Array ℕ := #[
    2121334051319427639067139270246400, 928455029464035206174343168, 19381498740061734928889413632, 1005826281919371473355538432, 20851552536713124005332123648, 31219300365728183807612289024,
    967140655691703339764940800, 31219300365728183807612289024, 32534611657468900349692608512, 19381498740061734928889413632, 967140655691703339764940800, 3597763239173136423925579776,
    4061990753905154027012751360, 3481706360490132023153786880, 45842467079786738304858193920, 4061990753905154027012751360, 3481706360490132023153786880, 4061990753905154027012751360,
    4061990753905154027012751360, 168398530969039385519871492096, 4178047632588158427784544256, 45842467079786738304858193920, 168398530969039385519871492096, 3597763239173136423925579776,
    4061990753905154027012751360, 4178047632588158427784544256, 4061990753905154027012751360, 696341272098026404630757376, 793055337667196738607251456, 618970019642690137449562112,
    8298066825834814655183192064, 735026898325694538221355008, 618970019642690137449562112, 735026898325694538221355008, 715684085211860471426056192, 27041252733140025379827744768,
    715684085211860471426056192, 8298066825834814655183192064, 27041252733140025379827744768, 696341272098026404630757376, 715684085211860471426056192, 715684085211860471426056192,
    793055337667196738607251456, 400498361509606226535364668948480, 860417801572475859454022819774464, 860417888237345553077751781523456, 304287126222753269864753438654464, 1112103357156887238762843326119936,
    304286750105152375228990748622848, 4967046202438780066192389308416
  ]
def positiveScales : Array ℕ := #[
    14, 1, 8, 3, 9, 9,
    4, 9, 9, 8, 4, 6,
    6, 5, 10, 6, 5, 6,
    6, 12, 4, 10, 12, 6,
    6, 4, 6, 3, 5, 0,
    8, 4, 0, 4, 5, 9,
    5, 8, 9, 3, 5, 5,
    5, 12, 34, 34, 34, 36,
    32, 28
  ]
def negativeArguments : Array ℕ := #[
    1185, 4353, 262613711, 25, 25, 105,
    27, 105, 1, 3, 1, 5055,
    2715, 10859
  ]
def negativeCoefficients : Array ℕ := #[
    22921233539893369152429096960, 84199265484519692759935746048, 2480316373536830917644189171712, 241785163922925834941235200, 241785163922925834941235200, 2030995376952577013506375680,
    2089023816294079213892272128, 2030995376952577013506375680, 158456325028528675187087900672, 475368975085586025561263702016, 79228162514264337593543950336, 400498361509606226535364668948480,
    1720835689809821412531774601297920, 1720677233484792883856587513397248
  ]
def negativeScales : Array ℕ := #[
    10, 12, 27, 4, 4, 6,
    4, 6, 0, 1, 0, 12,
    11, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14708598954519486, 1584962500720924, 8968666792316714, 3700439718136550, 9074141462752505, 9656424863276222,
    4643856189773592, 9656424863276222, 9715961990248632, 8968666792316714, 4643856189773592, 6539158811107971,
    6714245517659862, 5491853096329661, 10210671343785621, 6714245517659862, 5491853096329661, 6714245517659862,
    6714245517659862, 12087794304787900, 4754887502147955, 10210671343785621, 12087794304787900, 6539158811107971,
    6714245517659862, 4754887502147955, 6714245517659862, 3169925001442312, 5357552004618083, 0,
    8744833837487090, 4247927513443585, 0, 4247927513443585, 5209453365628949, 9449148645375433,
    5209453365628949, 8744833837487090, 9449148645375433, 3169925001442312, 5209453365628949, 5209453365628949,
    5357552004618083, 12303495376790376, 34406736410034593, 34406736555348848, 34907132333702701, 36776918007384574,
    32907130550441816, 28970231012208556
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10210671343785622, 12087794304787901, 27968367014232028, 4643856189792934, 4643856189792934, 6714245517766967,
    4754887502413606, 6714245517766967, 0, 1584962500724866, 0, 12303495376790378,
    11406736482691733, 13406603631727885
  ]

abbrev PositiveTerm := Fin 50
abbrev NegativeTerm := Fin 14
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
noncomputable def positiveFloor : ℝ := 945052639173 / 500000000000
noncomputable def negativeCeiling : ℝ := 143531438997 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 22921233539893369152429096960, coefficient := (-22921233539893369152429096960) }, { argument := 84199265484519692759935746048, coefficient := (-84199265484519692759935746048) }, { argument := 2480316373536830917644189171712, coefficient := (-2480316373536830917644189171712) }, { argument := 241785163922925834941235200, coefficient := (-241785163922925834941235200) }, { argument := 241785163922925834941235200, coefficient := (-241785163922925834941235200) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2121334051319427639067139270246400, coefficient := 2121334051319427639067139270246400 }, { argument := 928455029464035206174343168, coefficient := 928455029464035206174343168 }, { argument := 19381498740061734928889413632, coefficient := 19381498740061734928889413632 }, { argument := 1005826281919371473355538432, coefficient := 1005826281919371473355538432 }, { argument := 20851552536713124005332123648, coefficient := 20851552536713124005332123648 }, { argument := 31219300365728183807612289024, coefficient := 31219300365728183807612289024 }, { argument := 967140655691703339764940800, coefficient := 967140655691703339764940800 }, { argument := 31219300365728183807612289024, coefficient := 31219300365728183807612289024 }, { argument := 32534611657468900349692608512, coefficient := 32534611657468900349692608512 }, { argument := 19381498740061734928889413632, coefficient := 19381498740061734928889413632 }, { argument := 967140655691703339764940800, coefficient := 967140655691703339764940800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 793055337667196738607251456, coefficient := 793055337667196738607251456 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 8298066825834814655183192064, coefficient := 8298066825834814655183192064 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 27041252733140025379827744768, coefficient := 27041252733140025379827744768 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 8298066825834814655183192064, coefficient := 8298066825834814655183192064 }, { argument := 27041252733140025379827744768, coefficient := 27041252733140025379827744768 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 793055337667196738607251456, coefficient := 793055337667196738607251456 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 400498361509606226535364668948480, coefficient := 400498361509606226535364668948480 }, { argument := 400498361509606226535364668948480, coefficient := (-400498361509606226535364668948480) }, { argument := 860417801572475859454022819774464, coefficient := 860417801572475859454022819774464 }, { argument := 860417888237345553077751781523456, coefficient := 860417888237345553077751781523456 }, { argument := 1720835689809821412531774601297920, coefficient := (-1720835689809821412531774601297920) }, { argument := 304287126222753269864753438654464, coefficient := 304287126222753269864753438654464 }, { argument := 1112103357156887238762843326119936, coefficient := 1112103357156887238762843326119936 }, { argument := 304286750105152375228990748622848, coefficient := 304286750105152375228990748622848 }, { argument := 1720677233484792883856587513397248, coefficient := (-1720677233484792883856587513397248) }, { argument := 4967046202438780066192389308416, coefficient := 4967046202438780066192389308416 }] }

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


end Parent0

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-11151141873290391431046996233814016)
def positiveArguments : Array ℕ := #[
    41293871555, 41293879365, 525911251
  ]
def positiveCoefficients : Array ℕ := #[
    195004794979256237262783150817280, 195004831860938468474712269783040, 4967091329372890368522051387392
  ]
def positiveScales : Array ℕ := #[
    35, 35, 28
  ]
def negativeArguments : Array ℕ := #[
    631
  ]
def negativeCoefficients : Array ℕ := #[
    399943764372006376172209861296128
  ]
def negativeScales : Array ℕ := #[
    9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    35265208635281987, 35265208908142021, 28970244119416479
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    9301496194982550
  ]

abbrev PositiveTerm := Fin 3
abbrev NegativeTerm := Fin 1
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
noncomputable def positiveFloor : ℝ := 8364355133 / 50000000000
noncomputable def negativeCeiling : ℝ := 2798673677 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 195004794979256237262783150817280, coefficient := 195004794979256237262783150817280 }, { argument := 195004831860938468474712269783040, coefficient := 195004831860938468474712269783040 }, { argument := 4967091329372890368522051387392, coefficient := 4967091329372890368522051387392 }, { argument := 399943764372006376172209861296128, coefficient := (-399943764372006376172209861296128) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
