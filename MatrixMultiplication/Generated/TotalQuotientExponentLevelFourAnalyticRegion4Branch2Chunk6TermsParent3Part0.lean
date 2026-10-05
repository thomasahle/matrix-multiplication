import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 6, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6

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
def constantNumerator : ℤ := (-25434331738385701625877848129536)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    275834762935, 24920964126999, 24916743638029, 275834762935, 73017570879, 2114946270943,
    3981825, 24085097837441, 6792525, 3981825, 31620375, 31620375,
    6792525, 574085475, 6792525, 2114978829789, 31620375, 3981825,
    6792525, 3981825, 31620375, 31620375, 18679642721, 73017570879,
    696765802249, 2787062428009, 18253758221, 486260308265, 43932373025481, 43924932860051,
    486260308265, 696765802249, 10231994331453, 138624443, 29344789083823, 236476991,
    138624443, 1100841165, 1100841165, 236476991, 19986382929, 236476991,
    81857121664047, 1100841165, 138624443, 236476991, 138624443, 1100841165,
    1100841165, 2865431615461, 2114946270943, 10231994331453, 81855913903377, 264357770565,
    3981825, 138624443, 34656149, 248863, 275834762935, 486260308265,
    275770808055, 275770808055, 24915185967447, 24910966457037
  ]
def negativeCoefficients : Array ℕ := #[
    155281166946236887696670720, 7014627797254137159660601344, 7013439835219598829131137024, 155281166946236887696670720, 20552619062635198754586624, 595304452357969679491268608,
    36725853360649267681689600, 6779352352867576665180471296, 31324992572318493022617600, 4590731670081158460211200, 36455810321232728948736000, 36455810321232728948736000,
    31324992572318493022617600, 661875489609936434469273600, 31324992572318493022617600, 595313616858389255326531584, 36455810321232728948736000, 4590731670081158460211200,
    31324992572318493022617600, 4590731670081158460211200, 36455810321232728948736000, 36455810321232728948736000, 21031407999427399494139904, 20552619062635198754586624,
    784488551843275275948261376, 784488332014977639623163904, 20551904680551681993211904, 547480435776829129081487360, 24731727348382232696504451072, 24727538907599967340736806912,
    547480435776829129081487360, 784488551843275275948261376, 23040402929194379069928505344, 1278584811190768768273874944, 264314362366342123020842172416, 1090557633074479243527716864,
    159823101398846096034234368, 1269183452284954292036567040, 1269183452284954292036567040, 1090557633074479243527716864, 23042730678151281257641672704, 1090557633074479243527716864,
    23040731413988964041156984832, 1269183452284954292036567040, 159823101398846096034234368, 1090557633074479243527716864, 159823101398846096034234368, 1269183452284954292036567040,
    1269183452284954292036567040, 806547297227862374053052416, 595304452357969679491268608, 23040402929194379069928505344, 23040391459582503744870285312, 595280778504514537909125120,
    36725853360649267681689600, 1278584811190768768273874944, 1278586222366690407054573568, 36725696563324641150500864, 155281166946236887696670720, 547480435776829129081487360,
    155245163549519822098268160, 155245163549519822098268160, 7013001389928807505154015232, 7011813703334422384604086272
  ]
def negativeScales : Array ℕ := #[
    38, 44, 44, 38, 36, 40,
    21, 44, 22, 21, 24, 24,
    22, 29, 22, 40, 24, 21,
    22, 21, 24, 24, 34, 36,
    39, 41, 34, 38, 45, 45,
    38, 39, 43, 27, 44, 27,
    27, 30, 30, 27, 34, 27,
    46, 30, 27, 27, 27, 30,
    30, 41, 40, 43, 46, 37,
    21, 27, 25, 17, 38, 38,
    38, 38, 44, 44
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    38005013332206417, 44502425117079860, 44502180768822494, 38005013332206417, 36087524623410423, 40943758160955770,
    21924998392558141, 44453206017925850, 22695516539709145, 21924998392558141, 24914351147203807, 24914351147203807,
    22695516539709145, 29096690313383294, 22695516539709145, 40943780370565651, 24914351147203807, 21924998392558141,
    22695516539709145, 21924998392558141, 24914351147203807, 24914351147203807, 34120747810261089, 36087524623410423,
    39341882860957663, 41341882456687596, 34087474476351392, 38822937878997163, 45320349662846408, 45320105314589044,
    38822937878997163, 39341882860957663, 43218152603611946, 27046606422676130, 44738169572466010, 27817124577465684,
    27046606422676130, 30035959178476622, 30035959178476622, 27817124577465684, 34218298350292631, 27817124577465684,
    46218173171828893, 30035959178476622, 27046606422676130, 27817124577465684, 27046606422676130, 30035959178476622,
    30035959178476622, 41381889604885482, 40943758160955770, 43218152603611946, 46218151885431958, 37943700787228055,
    21924998392558141, 27046606422676130, 25046608014979873, 17924992233103382, 38005013332206417, 38822937878997163,
    38004678791028871, 38004678791028871, 44502090575902310, 44501846227644944
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
noncomputable def negativeCeiling : ℝ := 256398489 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 155281166946236887696670720, coefficient := (-155281166946236887696670720) }, { argument := 7014627797254137159660601344, coefficient := (-7014627797254137159660601344) }, { argument := 7013439835219598829131137024, coefficient := (-7013439835219598829131137024) }, { argument := 155281166946236887696670720, coefficient := (-155281166946236887696670720) }, { argument := 20552619062635198754586624, coefficient := (-20552619062635198754586624) }, { argument := 595304452357969679491268608, coefficient := (-595304452357969679491268608) }, { argument := 36725853360649267681689600, coefficient := (-36725853360649267681689600) }, { argument := 6779352352867576665180471296, coefficient := (-6779352352867576665180471296) }, { argument := 31324992572318493022617600, coefficient := (-31324992572318493022617600) }, { argument := 4590731670081158460211200, coefficient := (-4590731670081158460211200) }, { argument := 36455810321232728948736000, coefficient := (-36455810321232728948736000) }, { argument := 36455810321232728948736000, coefficient := (-36455810321232728948736000) }, { argument := 31324992572318493022617600, coefficient := (-31324992572318493022617600) }, { argument := 661875489609936434469273600, coefficient := (-661875489609936434469273600) }, { argument := 31324992572318493022617600, coefficient := (-31324992572318493022617600) }, { argument := 595313616858389255326531584, coefficient := (-595313616858389255326531584) }, { argument := 36455810321232728948736000, coefficient := (-36455810321232728948736000) }, { argument := 4590731670081158460211200, coefficient := (-4590731670081158460211200) }, { argument := 31324992572318493022617600, coefficient := (-31324992572318493022617600) }, { argument := 4590731670081158460211200, coefficient := (-4590731670081158460211200) }, { argument := 36455810321232728948736000, coefficient := (-36455810321232728948736000) }, { argument := 36455810321232728948736000, coefficient := (-36455810321232728948736000) }, { argument := 21031407999427399494139904, coefficient := (-21031407999427399494139904) }, { argument := 20552619062635198754586624, coefficient := (-20552619062635198754586624) }, { argument := 784488551843275275948261376, coefficient := (-784488551843275275948261376) }, { argument := 784488332014977639623163904, coefficient := (-784488332014977639623163904) }, { argument := 20551904680551681993211904, coefficient := (-20551904680551681993211904) }, { argument := 547480435776829129081487360, coefficient := (-547480435776829129081487360) }, { argument := 24731727348382232696504451072, coefficient := (-24731727348382232696504451072) }, { argument := 24727538907599967340736806912, coefficient := (-24727538907599967340736806912) }, { argument := 547480435776829129081487360, coefficient := (-547480435776829129081487360) }, { argument := 784488551843275275948261376, coefficient := (-784488551843275275948261376) }, { argument := 23040402929194379069928505344, coefficient := (-23040402929194379069928505344) }, { argument := 1278584811190768768273874944, coefficient := (-1278584811190768768273874944) }, { argument := 264314362366342123020842172416, coefficient := (-264314362366342123020842172416) }, { argument := 1090557633074479243527716864, coefficient := (-1090557633074479243527716864) }, { argument := 159823101398846096034234368, coefficient := (-159823101398846096034234368) }, { argument := 1269183452284954292036567040, coefficient := (-1269183452284954292036567040) }, { argument := 1269183452284954292036567040, coefficient := (-1269183452284954292036567040) }, { argument := 1090557633074479243527716864, coefficient := (-1090557633074479243527716864) }, { argument := 23042730678151281257641672704, coefficient := (-23042730678151281257641672704) }, { argument := 1090557633074479243527716864, coefficient := (-1090557633074479243527716864) }, { argument := 23040731413988964041156984832, coefficient := (-23040731413988964041156984832) }, { argument := 1269183452284954292036567040, coefficient := (-1269183452284954292036567040) }, { argument := 159823101398846096034234368, coefficient := (-159823101398846096034234368) }, { argument := 1090557633074479243527716864, coefficient := (-1090557633074479243527716864) }, { argument := 159823101398846096034234368, coefficient := (-159823101398846096034234368) }, { argument := 1269183452284954292036567040, coefficient := (-1269183452284954292036567040) }, { argument := 1269183452284954292036567040, coefficient := (-1269183452284954292036567040) }, { argument := 806547297227862374053052416, coefficient := (-806547297227862374053052416) }, { argument := 595304452357969679491268608, coefficient := (-595304452357969679491268608) }, { argument := 23040402929194379069928505344, coefficient := (-23040402929194379069928505344) }, { argument := 23040391459582503744870285312, coefficient := (-23040391459582503744870285312) }, { argument := 595280778504514537909125120, coefficient := (-595280778504514537909125120) }, { argument := 36725853360649267681689600, coefficient := (-36725853360649267681689600) }, { argument := 1278584811190768768273874944, coefficient := (-1278584811190768768273874944) }, { argument := 1278586222366690407054573568, coefficient := (-1278586222366690407054573568) }, { argument := 36725696563324641150500864, coefficient := (-36725696563324641150500864) }, { argument := 155281166946236887696670720, coefficient := (-155281166946236887696670720) }, { argument := 547480435776829129081487360, coefficient := (-547480435776829129081487360) }, { argument := 155245163549519822098268160, coefficient := (-155245163549519822098268160) }, { argument := 155245163549519822098268160, coefficient := (-155245163549519822098268160) }, { argument := 7013001389928807505154015232, coefficient := (-7013001389928807505154015232) }, { argument := 7011813703334422384604086272, coefficient := (-7011813703334422384604086272) }] }

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
def constantNumerator : ℤ := (-50562742124432106836002525413376)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    275770808055, 2787062428009, 81855913903377, 34656149, 939032691313055, 59119313,
    34656149, 275210595, 275210595, 59119313, 4996601247, 59119313,
    81857080915761, 275210595, 34656149, 59119313, 34656149, 275210595,
    275210595, 1432715355227, 24085097837441, 29344789083823, 939032691313055, 94078432813,
    6792525, 236476991, 59119313, 424531, 24920964126999, 43932373025481,
    24915185967447, 3981825, 138624443, 34656149, 248863, 31620375,
    1100841165, 275210595, 1976265, 31620375, 1100841165, 275210595,
    1976265, 6792525, 236476991, 59119313, 424531, 574085475,
    19986382929, 4996601247, 35880189, 6792525, 236476991, 59119313,
    424531, 18253758221, 264357770565, 248863, 94078432813, 424531,
    248863, 1976265, 1976265, 424531
  ]
def negativeCoefficients : Array ℕ := #[
    155245163549519822098268160, 784488332014977639623163904, 23040391459582503744870285312, 1278586222366690407054573568, 264314204917886780889450414080, 1090558836724530053075959808,
    159823277795836300881821696, 1269184853084582389355642880, 1269184853084582389355642880, 1090558836724530053075959808, 23042756110446751380079116288, 1090558836724530053075959808,
    23040719944366111192007049216, 1269184853084582389355642880, 159823277795836300881821696, 1090558836724530053075959808, 159823277795836300881821696, 1269184853084582389355642880,
    1269184853084582389355642880, 806547042491038126072397824, 6779352352867576665180471296, 264314362366342123020842172416, 264314204917886780889450414080, 6779065519363632700711763968,
    31324992572318493022617600, 1090557633074479243527716864, 1090558836724530053075959808, 31324858833423958628368384, 7014627797254137159660601344, 24731727348382232696504451072,
    7013001389928807505154015232, 4590731670081158460211200, 159823101398846096034234368, 159823277795836300881821696, 4590712070415580143812608, 36455810321232728948736000,
    1269183452284954292036567040, 1269184853084582389355642880, 36455654676829607024394240, 36455810321232728948736000, 1269183452284954292036567040, 1269184853084582389355642880,
    36455654676829607024394240, 31324992572318493022617600, 1090557633074479243527716864, 1090558836724530053075959808, 31324858833423958628368384, 661875489609936434469273600,
    23042730678151281257641672704, 23042756110446751380079116288, 661872663799328643087335424, 31324992572318493022617600, 1090557633074479243527716864, 1090558836724530053075959808,
    31324858833423958628368384, 20551904680551681993211904, 595280778504514537909125120, 36725696563324641150500864, 6779065519363632700711763968, 31324858833423958628368384,
    4590712070415580143812608, 36455654676829607024394240, 36455654676829607024394240, 31324858833423958628368384
  ]
def negativeScales : Array ℕ := #[
    38, 41, 46, 25, 49, 25,
    25, 28, 28, 25, 32, 25,
    46, 28, 25, 25, 25, 28,
    28, 40, 44, 44, 49, 36,
    22, 27, 25, 18, 44, 45,
    44, 21, 27, 25, 17, 24,
    30, 28, 20, 24, 30, 28,
    20, 22, 27, 25, 18, 29,
    34, 32, 25, 22, 27, 25,
    18, 34, 37, 17, 36, 18,
    17, 20, 20, 18
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    38004678791028871, 41341882456687596, 46218151885431958, 25046608014979873, 49738168713072021, 25817126169769456,
    25046608014979873, 28035960770780365, 28035960770780365, 25817126169769456, 32218299942596373, 25817126169769456,
    46218172453658456, 28035960770780365, 25046608014979873, 25817126169769456, 25046608014979873, 28035960770780365,
    28035960770780365, 40381889149230107, 44453206017925850, 44738169572466010, 49738168713072021, 36453144976397604,
    22695516539709145, 27817124577465684, 25817126169769456, 18695510380255104, 44502425117079860, 45320349662846408,
    44502090575902310, 21924998392558141, 27046606422676130, 25046608014979873, 17924992233103382, 24914351147203807,
    30035959178476622, 28035960770780365, 20914344987749163, 24914351147203807, 30035959178476622, 28035960770780365,
    20914344987749163, 22695516539709145, 27817124577465684, 25817126169769456, 18695510380255104, 29096690313383294,
    34218298350292631, 32218299942596373, 25096684153929262, 22695516539709145, 27817124577465684, 25817126169769456,
    18695510380255104, 34087474476351392, 37943700787228055, 17924992233103382, 36453144976397604, 18695510380255104,
    17924992233103382, 20914344987749163, 20914344987749163, 18695510380255104
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
noncomputable def negativeCeiling : ℝ := 276060459 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 155245163549519822098268160, coefficient := (-155245163549519822098268160) }, { argument := 784488332014977639623163904, coefficient := (-784488332014977639623163904) }, { argument := 23040391459582503744870285312, coefficient := (-23040391459582503744870285312) }, { argument := 1278586222366690407054573568, coefficient := (-1278586222366690407054573568) }, { argument := 264314204917886780889450414080, coefficient := (-264314204917886780889450414080) }, { argument := 1090558836724530053075959808, coefficient := (-1090558836724530053075959808) }, { argument := 159823277795836300881821696, coefficient := (-159823277795836300881821696) }, { argument := 1269184853084582389355642880, coefficient := (-1269184853084582389355642880) }, { argument := 1269184853084582389355642880, coefficient := (-1269184853084582389355642880) }, { argument := 1090558836724530053075959808, coefficient := (-1090558836724530053075959808) }, { argument := 23042756110446751380079116288, coefficient := (-23042756110446751380079116288) }, { argument := 1090558836724530053075959808, coefficient := (-1090558836724530053075959808) }, { argument := 23040719944366111192007049216, coefficient := (-23040719944366111192007049216) }, { argument := 1269184853084582389355642880, coefficient := (-1269184853084582389355642880) }, { argument := 159823277795836300881821696, coefficient := (-159823277795836300881821696) }, { argument := 1090558836724530053075959808, coefficient := (-1090558836724530053075959808) }, { argument := 159823277795836300881821696, coefficient := (-159823277795836300881821696) }, { argument := 1269184853084582389355642880, coefficient := (-1269184853084582389355642880) }, { argument := 1269184853084582389355642880, coefficient := (-1269184853084582389355642880) }, { argument := 806547042491038126072397824, coefficient := (-806547042491038126072397824) }, { argument := 6779352352867576665180471296, coefficient := (-6779352352867576665180471296) }, { argument := 264314362366342123020842172416, coefficient := (-264314362366342123020842172416) }, { argument := 264314204917886780889450414080, coefficient := (-264314204917886780889450414080) }, { argument := 6779065519363632700711763968, coefficient := (-6779065519363632700711763968) }, { argument := 31324992572318493022617600, coefficient := (-31324992572318493022617600) }, { argument := 1090557633074479243527716864, coefficient := (-1090557633074479243527716864) }, { argument := 1090558836724530053075959808, coefficient := (-1090558836724530053075959808) }, { argument := 31324858833423958628368384, coefficient := (-31324858833423958628368384) }, { argument := 7014627797254137159660601344, coefficient := (-7014627797254137159660601344) }, { argument := 24731727348382232696504451072, coefficient := (-24731727348382232696504451072) }, { argument := 7013001389928807505154015232, coefficient := (-7013001389928807505154015232) }, { argument := 4590731670081158460211200, coefficient := (-4590731670081158460211200) }, { argument := 159823101398846096034234368, coefficient := (-159823101398846096034234368) }, { argument := 159823277795836300881821696, coefficient := (-159823277795836300881821696) }, { argument := 4590712070415580143812608, coefficient := (-4590712070415580143812608) }, { argument := 36455810321232728948736000, coefficient := (-36455810321232728948736000) }, { argument := 1269183452284954292036567040, coefficient := (-1269183452284954292036567040) }, { argument := 1269184853084582389355642880, coefficient := (-1269184853084582389355642880) }, { argument := 36455654676829607024394240, coefficient := (-36455654676829607024394240) }, { argument := 36455810321232728948736000, coefficient := (-36455810321232728948736000) }, { argument := 1269183452284954292036567040, coefficient := (-1269183452284954292036567040) }, { argument := 1269184853084582389355642880, coefficient := (-1269184853084582389355642880) }, { argument := 36455654676829607024394240, coefficient := (-36455654676829607024394240) }, { argument := 31324992572318493022617600, coefficient := (-31324992572318493022617600) }, { argument := 1090557633074479243527716864, coefficient := (-1090557633074479243527716864) }, { argument := 1090558836724530053075959808, coefficient := (-1090558836724530053075959808) }, { argument := 31324858833423958628368384, coefficient := (-31324858833423958628368384) }, { argument := 661875489609936434469273600, coefficient := (-661875489609936434469273600) }, { argument := 23042730678151281257641672704, coefficient := (-23042730678151281257641672704) }, { argument := 23042756110446751380079116288, coefficient := (-23042756110446751380079116288) }, { argument := 661872663799328643087335424, coefficient := (-661872663799328643087335424) }, { argument := 31324992572318493022617600, coefficient := (-31324992572318493022617600) }, { argument := 1090557633074479243527716864, coefficient := (-1090557633074479243527716864) }, { argument := 1090558836724530053075959808, coefficient := (-1090558836724530053075959808) }, { argument := 31324858833423958628368384, coefficient := (-31324858833423958628368384) }, { argument := 20551904680551681993211904, coefficient := (-20551904680551681993211904) }, { argument := 595280778504514537909125120, coefficient := (-595280778504514537909125120) }, { argument := 36725696563324641150500864, coefficient := (-36725696563324641150500864) }, { argument := 6779065519363632700711763968, coefficient := (-6779065519363632700711763968) }, { argument := 31324858833423958628368384, coefficient := (-31324858833423958628368384) }, { argument := 4590712070415580143812608, coefficient := (-4590712070415580143812608) }, { argument := 36455654676829607024394240, coefficient := (-36455654676829607024394240) }, { argument := 36455654676829607024394240, coefficient := (-36455654676829607024394240) }, { argument := 31324858833423958628368384, coefficient := (-31324858833423958628368384) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6
