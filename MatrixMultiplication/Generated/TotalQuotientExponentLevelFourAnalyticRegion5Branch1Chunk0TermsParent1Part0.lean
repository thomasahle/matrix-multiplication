import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 0, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 178675, 8209961, 1026231, 44683, 38201,
    1276761, 7073665, 638373, 19089
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 1687537662653467717114265600, 77540889304133910576561651712, 77539822049308782036743356416, 1688076012432514856668626944, 360798244024206633616801792,
    12058666706070262185367437312, 133617754028192435642155663360, 12058525035075776096011026432, 360581015165994629936971776
  ]
def positiveScales : Array ℕ := #[
    0, 17, 22, 19, 15, 15,
    20, 22, 19, 14
  ]
def negativeArguments : Array ℕ := #[
    6825563675, 228125271675, 1263887093875, 114061295775, 3410727075, 6825563675,
    313628720161, 39203050431, 1706935283, 313628720161, 10482158016321, 58074513777065,
    5241017433453, 156719945529, 228125271675, 10482158016321, 1310251717791, 57049511763,
    39203050431, 1310251717791, 7259214306615, 655118162163, 19589723559, 1263887093875,
    58074513777065, 7259214306615, 316072573195, 1706935283, 57049511763, 316072573195,
    28524420759, 852953787, 114061295775, 5241017433453, 655118162163, 28524420759,
    3410727075, 156719945529, 19589723559, 852953787, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1921225376457724579020800, 64211555531832697867468800, 711505180626728637169664000, 64210801143710741220556800, 1920068648004057720422400, 1921225376457724579020800,
    88278636703110322890735616, 88277421656419181304741888, 1921838276116088033902592, 88278636703110322890735616, 2950465183521369570542616576, 32693044825764083776387809280,
    2950430520042650514631950336, 88225486035741103827714048, 64211555531832697867468800, 2950465183521369570542616576, 2950424574002549942195847168, 64232039979378882077786112,
    88277421656419181304741888, 2950424574002549942195847168, 32692594846273887496348631040, 2950389911000930971809742848, 88224271720603426712715264, 711505180626728637169664000,
    32693044825764083776387809280, 32692594846273887496348631040, 711732161431517911171727360, 1921838276116088033902592, 64232039979378882077786112, 711732161431517911171727360,
    64231285350595820343263232, 1920681178648726707634176, 64210801143710741220556800, 2950430520042650514631950336, 2950389911000930971809742848, 64231285350595820343263232,
    1920068648004057720422400, 88225486035741103827714048, 88224271720603426712715264, 1920681178648726707634176, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    32, 37, 40, 36, 31, 32,
    38, 35, 30, 38, 43, 45,
    42, 37, 37, 43, 40, 35,
    35, 40, 42, 39, 34, 40,
    45, 42, 38, 30, 35, 38,
    34, 29, 36, 42, 39, 34,
    31, 37, 34, 29, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 17446978262710127, 22968943937187703, 19968924080131235, 15447438430630889, 15221322784202037,
    20284057058041302, 22754026465718032, 19284040108469115, 14220453906972867
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32668301046945881, 37731035320899165, 40201004728443390, 36731018371326922, 31667432169715993, 32668301046945881,
    38190266722272261, 35190246865215504, 30668761214867028, 38190266722272261, 43253000996111526, 45722970403926603,
    42252984046539338, 37189397845043090, 37731035320899165, 43253000996111526, 40252981139054769, 35731495488821461,
    35190246865215504, 40252981139054769, 42722950546869791, 39252964189482582, 34189377987986333, 40201004728443390,
    45722970403926603, 42722950546869791, 38201464896364152, 30668761214867028, 35731495488821461, 38201464896364152,
    34731478539249217, 29667892337637133, 36731018371326922, 42252984046539338, 39252964189482582, 34731478539249217,
    31667432169715993, 37189397845043090, 34189377987986333, 29667892337637133, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 41606317 / 500000000000
noncomputable def negativeCeiling : ℝ := 16642527 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1921225376457724579020800, coefficient := (-1921225376457724579020800) }, { argument := 64211555531832697867468800, coefficient := (-64211555531832697867468800) }, { argument := 711505180626728637169664000, coefficient := (-711505180626728637169664000) }, { argument := 64210801143710741220556800, coefficient := (-64210801143710741220556800) }, { argument := 1920068648004057720422400, coefficient := (-1920068648004057720422400) }, { argument := 1921225376457724579020800, coefficient := (-1921225376457724579020800) }, { argument := 88278636703110322890735616, coefficient := (-88278636703110322890735616) }, { argument := 88277421656419181304741888, coefficient := (-88277421656419181304741888) }, { argument := 1921838276116088033902592, coefficient := (-1921838276116088033902592) }, { argument := 88278636703110322890735616, coefficient := (-88278636703110322890735616) }, { argument := 2950465183521369570542616576, coefficient := (-2950465183521369570542616576) }, { argument := 32693044825764083776387809280, coefficient := (-32693044825764083776387809280) }, { argument := 2950430520042650514631950336, coefficient := (-2950430520042650514631950336) }, { argument := 88225486035741103827714048, coefficient := (-88225486035741103827714048) }, { argument := 64211555531832697867468800, coefficient := (-64211555531832697867468800) }, { argument := 2950465183521369570542616576, coefficient := (-2950465183521369570542616576) }, { argument := 2950424574002549942195847168, coefficient := (-2950424574002549942195847168) }, { argument := 64232039979378882077786112, coefficient := (-64232039979378882077786112) }, { argument := 88277421656419181304741888, coefficient := (-88277421656419181304741888) }, { argument := 2950424574002549942195847168, coefficient := (-2950424574002549942195847168) }, { argument := 32692594846273887496348631040, coefficient := (-32692594846273887496348631040) }, { argument := 2950389911000930971809742848, coefficient := (-2950389911000930971809742848) }, { argument := 88224271720603426712715264, coefficient := (-88224271720603426712715264) }, { argument := 711505180626728637169664000, coefficient := (-711505180626728637169664000) }, { argument := 32693044825764083776387809280, coefficient := (-32693044825764083776387809280) }, { argument := 32692594846273887496348631040, coefficient := (-32692594846273887496348631040) }, { argument := 711732161431517911171727360, coefficient := (-711732161431517911171727360) }, { argument := 1921838276116088033902592, coefficient := (-1921838276116088033902592) }, { argument := 64232039979378882077786112, coefficient := (-64232039979378882077786112) }, { argument := 711732161431517911171727360, coefficient := (-711732161431517911171727360) }, { argument := 64231285350595820343263232, coefficient := (-64231285350595820343263232) }, { argument := 1920681178648726707634176, coefficient := (-1920681178648726707634176) }, { argument := 64210801143710741220556800, coefficient := (-64210801143710741220556800) }, { argument := 2950430520042650514631950336, coefficient := (-2950430520042650514631950336) }, { argument := 2950389911000930971809742848, coefficient := (-2950389911000930971809742848) }, { argument := 64231285350595820343263232, coefficient := (-64231285350595820343263232) }, { argument := 1920068648004057720422400, coefficient := (-1920068648004057720422400) }, { argument := 88225486035741103827714048, coefficient := (-88225486035741103827714048) }, { argument := 88224271720603426712715264, coefficient := (-88224271720603426712715264) }, { argument := 1920681178648726707634176, coefficient := (-1920681178648726707634176) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 1687537662653467717114265600, coefficient := 1687537662653467717114265600 }, { argument := 77540889304133910576561651712, coefficient := 77540889304133910576561651712 }, { argument := 77539822049308782036743356416, coefficient := 77539822049308782036743356416 }, { argument := 1688076012432514856668626944, coefficient := 1688076012432514856668626944 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 360798244024206633616801792, coefficient := 360798244024206633616801792 }, { argument := 12058666706070262185367437312, coefficient := 12058666706070262185367437312 }, { argument := 133617754028192435642155663360, coefficient := 133617754028192435642155663360 }, { argument := 12058525035075776096011026432, coefficient := 12058525035075776096011026432 }, { argument := 360581015165994629936971776, coefficient := 360581015165994629936971776 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0
