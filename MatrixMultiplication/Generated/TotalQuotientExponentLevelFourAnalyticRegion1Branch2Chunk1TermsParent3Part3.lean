import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2587361099508722173829141781020672)
def positiveArguments : Array ℕ := #[
    217, 703401839, 2191, 196823081, 4389, 1967,
    665, 217, 48549433, 5311, 469352619, 131419,
    4181, 469352845, 2147, 2147, 72659, 3955,
    131419, 72659, 48549207, 4181, 3955, 5311,
    861665, 29820259, 9639, 99557745, 9891, 315,
    9639, 5481, 9891, 154413, 189, 14910133,
    9639, 315, 189, 315, 4851, 5481,
    861665, 529085, 8731971, 105, 93, 4353,
    1185, 4365987, 4353, 105, 105, 45,
    105, 1185, 45, 264541, 93
  ]
def positiveCoefficients : Array ℕ := #[
    33579123565615939956638744576, 13286885073929881762365257547776, 678081656518567045575995293696, 3717882883078149169346200469504, 679164854052941753316532027392, 608757014318585750181644337152,
    823230126124777882807917608960, 33579123565615939956638744576, 917072860646101952144418537472, 410918721790290914999328047104, 17731640612901492933192258158592, 10168052626427836896685500399616,
    323489206515760933084577398784, 17731649150940093961510804520960, 332232158043213931276052463616, 332232158043213931276052463616, 5621717832152277837118466686976, 306003303460854936701627269120,
    10168052626427836896685500399616, 5621717832152277837118466686976, 917068591626801437985145356288, 323489206515760933084577398784, 306003303460854936701627269120, 410918721790290914999328047104,
    32552783323694982744474910720, 1126577532896735068084200538112, 745781502416986279359541149696, 3761185264784664051404935004160, 765279058035731018689202356224, 24371944523430924162076508160,
    745781502416986279359541149696, 424071834707698080420131241984, 765279058035731018689202356224, 11947127205385839024249904300032, 467941334849873743911868956672, 1126577797349258108784332505088,
    745781502416986279359541149696, 24371944523430924162076508160, 467941334849873743911868956672, 24371944523430924162076508160, 750655891321672464191956451328, 424071834707698080420131241984,
    32552783323694982744474910720, 4997066541178172475776696320, 82471134359579477572564549632, 4061990753905154027012751360, 3597763239173136423925579776, 168398530969039385519871492096,
    45842467079786738304858193920, 82471162693778374790435831808, 168398530969039385519871492096, 4061990753905154027012751360, 4061990753905154027012751360, 3481706360490132023153786880,
    4061990753905154027012751360, 45842467079786738304858193920, 3481706360490132023153786880, 4997038206979275257905414144, 3597763239173136423925579776
  ]
def positiveScales : Array ℕ := #[
    7, 29, 11, 27, 12, 10,
    9, 7, 25, 12, 28, 17,
    12, 28, 11, 11, 16, 11,
    17, 16, 25, 12, 11, 12,
    19, 24, 13, 26, 13, 8,
    13, 12, 13, 17, 7, 23,
    13, 8, 7, 8, 12, 12,
    19, 19, 23, 6, 6, 12,
    10, 22, 12, 6, 6, 5,
    6, 10, 5, 18, 6
  ]
def negativeArguments : Array ℕ := #[
    77, 113, 77, 1
  ]
def negativeCoefficients : Array ℕ := #[
    24402274054393415978811536703488, 71622258912894961184563731103744, 24402274054393415978811536703488, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    6, 6, 6, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7761551232426566, 29389773865902766, 11097373768990222, 27552324171298940, 12099676554859642, 10941781241718677,
    9377210530388551, 7761551232426566, 25532951110981292, 12374767814092824, 28806096968652454, 17003814343888406,
    12029632328044137, 28806097663330586, 11068106475858773, 11068106475858773, 16148853889743134, 11949461978722474,
    17003814343888406, 16148853889743134, 25532944395149242, 12029632328044137, 11949461978722474, 12374767814092824,
    19716767558621244, 24829789452155812, 13234667766192568, 26569030217610284, 13271900672391543, 8299208018387278,
    13234667766192568, 12420223419348643, 13271900672391543, 17236434692366755, 7562242424220952, 23829789790813638,
    13234667766192568, 8299208018387278, 7562242424220952, 8299208018387278, 12244066464194817, 12420223419348643,
    19716767558621244, 19013139991156978, 23057875908284845, 6714245517659862, 6539158811107971, 12087794304787900,
    10210671343785621, 22057876403944345, 12087794304787900, 6714245517659862, 6714245517659862, 5491853096329661,
    6714245517659862, 10210671343785621, 5491853096329661, 18013131810812812, 6539158811107971
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6266786540694902, 6820178963384638, 6266786540694902, 0
  ]

abbrev PositiveTerm := Fin 59
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
noncomputable def positiveFloor : ℝ := 978142883 / 31250000000
noncomputable def negativeCeiling : ℝ := 4780665537 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 13286885073929881762365257547776, coefficient := 13286885073929881762365257547776 }, { argument := 678081656518567045575995293696, coefficient := 678081656518567045575995293696 }, { argument := 3717882883078149169346200469504, coefficient := 3717882883078149169346200469504 }, { argument := 679164854052941753316532027392, coefficient := 679164854052941753316532027392 }, { argument := 608757014318585750181644337152, coefficient := 608757014318585750181644337152 }, { argument := 823230126124777882807917608960, coefficient := 823230126124777882807917608960 }, { argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 24402274054393415978811536703488, coefficient := (-24402274054393415978811536703488) }, { argument := 917072860646101952144418537472, coefficient := 917072860646101952144418537472 }, { argument := 410918721790290914999328047104, coefficient := 410918721790290914999328047104 }, { argument := 17731640612901492933192258158592, coefficient := 17731640612901492933192258158592 }, { argument := 10168052626427836896685500399616, coefficient := 10168052626427836896685500399616 }, { argument := 323489206515760933084577398784, coefficient := 323489206515760933084577398784 }, { argument := 17731649150940093961510804520960, coefficient := 17731649150940093961510804520960 }, { argument := 332232158043213931276052463616, coefficient := 332232158043213931276052463616 }, { argument := 332232158043213931276052463616, coefficient := 332232158043213931276052463616 }, { argument := 5621717832152277837118466686976, coefficient := 5621717832152277837118466686976 }, { argument := 306003303460854936701627269120, coefficient := 306003303460854936701627269120 }, { argument := 10168052626427836896685500399616, coefficient := 10168052626427836896685500399616 }, { argument := 5621717832152277837118466686976, coefficient := 5621717832152277837118466686976 }, { argument := 917068591626801437985145356288, coefficient := 917068591626801437985145356288 }, { argument := 323489206515760933084577398784, coefficient := 323489206515760933084577398784 }, { argument := 306003303460854936701627269120, coefficient := 306003303460854936701627269120 }, { argument := 410918721790290914999328047104, coefficient := 410918721790290914999328047104 }, { argument := 71622258912894961184563731103744, coefficient := (-71622258912894961184563731103744) }, { argument := 32552783323694982744474910720, coefficient := 32552783323694982744474910720 }, { argument := 1126577532896735068084200538112, coefficient := 1126577532896735068084200538112 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 3761185264784664051404935004160, coefficient := 3761185264784664051404935004160 }, { argument := 765279058035731018689202356224, coefficient := 765279058035731018689202356224 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 424071834707698080420131241984, coefficient := 424071834707698080420131241984 }, { argument := 765279058035731018689202356224, coefficient := 765279058035731018689202356224 }, { argument := 11947127205385839024249904300032, coefficient := 11947127205385839024249904300032 }, { argument := 467941334849873743911868956672, coefficient := 467941334849873743911868956672 }, { argument := 1126577797349258108784332505088, coefficient := 1126577797349258108784332505088 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 467941334849873743911868956672, coefficient := 467941334849873743911868956672 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 750655891321672464191956451328, coefficient := 750655891321672464191956451328 }, { argument := 424071834707698080420131241984, coefficient := 424071834707698080420131241984 }, { argument := 32552783323694982744474910720, coefficient := 32552783323694982744474910720 }, { argument := 24402274054393415978811536703488, coefficient := (-24402274054393415978811536703488) }, { argument := 4997066541178172475776696320, coefficient := 4997066541178172475776696320 }, { argument := 82471134359579477572564549632, coefficient := 82471134359579477572564549632 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 82471162693778374790435831808, coefficient := 82471162693778374790435831808 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 4997038206979275257905414144, coefficient := 4997038206979275257905414144 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
