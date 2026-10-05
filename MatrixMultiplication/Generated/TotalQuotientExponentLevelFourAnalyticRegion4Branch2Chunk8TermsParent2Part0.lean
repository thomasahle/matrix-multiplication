import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 8, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-40023807796850582751146867163136)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    151868038189, 1981411978557, 51053703, 2688075409855, 87091611, 51053703,
    405426465, 405426465, 87091611, 7360742709, 87091611, 15851553753523,
    405426465, 51053703, 87091611, 51053703, 405426465, 405426465,
    616620375025, 101895603975, 16660191959875, 8330088545725, 407559408935, 151868038189,
    2185262508465, 607403042203, 2185262508465, 57039564604605, 183105181, 619442516392571,
    312355897, 183105181, 1454070555, 1454070555, 312355897, 26399458743,
    312355897, 14260118719225, 1454070555, 183105181, 312355897, 183105181,
    1454070555, 1454070555, 2220367731507, 16660191959875, 334980450752325, 669960371113425,
    8329667081265, 1981411978557, 57039564604605, 15848868155739, 51053703, 183105181,
    12763447, 607403042203, 15848868155739, 12763447, 172007516771781, 21772939,
    12763447, 101356785, 101356785, 21772939
  ]
def negativeCoefficients : Array ℕ := #[
    170988210049367164044967936, 4461743124148371205323227136, 470887296628088778233217024, 48424061656667085244538552320, 401639164771016899081273344, 58860912078511097279152128,
    467424890035235184275619840, 467424890035235184275619840, 401639164771016899081273344, 8486358559084158790070697984, 401639164771016899081273344, 4461815723600598124711641088,
    467424890035235184275619840, 58860912078511097279152128, 401639164771016899081273344, 58860912078511097279152128, 467424890035235184275619840, 467424890035235184275619840,
    173563205699477843633766400, 114724251023125407753830400, 4689427143900873965436928000, 4689422958811293366301491200, 114717775138187849876111360, 170988210049367164044967936,
    615096713676855585055703040, 170968757158071028487815168, 615096713676855585055703040, 16055210118667150688130170880, 1688847206238632395038261248, 174357567875189069732774936576,
    1440487322968245278120869888, 211105900779829049379782656, 1676429212075113039192391680, 1676429212075113039192391680, 1440487322968245278120869888, 30436503694785941178226311168,
    1440487322968245278120869888, 16055466337540186168518246400, 1676429212075113039192391680, 211105900779829049379782656, 1440487322968245278120869888, 211105900779829049379782656,
    1676429212075113039192391680, 1676429212075113039192391680, 624977955515024919433838592, 4689427143900873965436928000, 188577229148071457058088550400, 188577079856213752646782156800,
    4689185695413167627886919680, 4461743124148371205323227136, 16055210118667150688130170880, 4461059795026892535348854784, 470887296628088778233217024, 1688847206238632395038261248,
    470888080614711910889160704, 170968757158071028487815168, 4461059795026892535348854784, 470888080614711910889160704, 48415811777394828291222798336, 401639833465489571052519424,
    58861010076838988861145088, 467425668257250793897328640, 467425668257250793897328640, 401639833465489571052519424
  ]
def negativeScales : Array ℕ := #[
    37, 40, 25, 41, 26, 25,
    28, 28, 26, 32, 26, 43,
    28, 25, 26, 25, 28, 28,
    39, 36, 43, 42, 38, 37,
    40, 39, 40, 45, 27, 49,
    28, 27, 30, 30, 28, 34,
    28, 43, 30, 27, 28, 27,
    30, 30, 41, 43, 48, 49,
    42, 40, 45, 43, 25, 27,
    23, 39, 43, 23, 47, 24,
    23, 26, 26, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37144027319143366, 40849666019398852, 25605512269904727, 41289710749941291, 26376030423775381, 25605512269904727,
    28594865025703540, 28594865025703540, 26376030423775381, 32777204197917594, 26376030423775381, 43849689494085337,
    28594865025703540, 25605512269904727, 26376030423775381, 25605512269904727, 28594865025703540, 28594865025703540,
    39165591605054713, 36568300855225078, 43921470263552483, 42921468976015399, 38568219416551927, 37144027319143366,
    40990943755516893, 39143863178081621, 40990943755516893, 45697028203022193, 27448097372174434, 49137963736433470,
    28218615526051623, 27448097372174434, 30437450127974911, 30437450127974911, 28218615526051623, 34619789299800578,
    28218615526051623, 43697051226249288, 30437450127974911, 27448097372174434, 28218615526051623, 27448097372174434,
    30437450127974911, 30437450127974911, 41013935770398085, 43921470263552483, 48251070231678170, 49251069089532276,
    42921395980376341, 40849666019398852, 45697028203022193, 43849445049468652, 25605512269904727, 27448097372174434,
    23605514671865197, 39143863178081621, 43849445049468652, 23605514671865197, 47289464940864498, 24376032825735850,
    23605514671865197, 26594867427664009, 26594867427664009, 24376032825735850
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
noncomputable def negativeCeiling : ℝ := 56214859 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 170988210049367164044967936, coefficient := (-170988210049367164044967936) }, { argument := 4461743124148371205323227136, coefficient := (-4461743124148371205323227136) }, { argument := 470887296628088778233217024, coefficient := (-470887296628088778233217024) }, { argument := 48424061656667085244538552320, coefficient := (-48424061656667085244538552320) }, { argument := 401639164771016899081273344, coefficient := (-401639164771016899081273344) }, { argument := 58860912078511097279152128, coefficient := (-58860912078511097279152128) }, { argument := 467424890035235184275619840, coefficient := (-467424890035235184275619840) }, { argument := 467424890035235184275619840, coefficient := (-467424890035235184275619840) }, { argument := 401639164771016899081273344, coefficient := (-401639164771016899081273344) }, { argument := 8486358559084158790070697984, coefficient := (-8486358559084158790070697984) }, { argument := 401639164771016899081273344, coefficient := (-401639164771016899081273344) }, { argument := 4461815723600598124711641088, coefficient := (-4461815723600598124711641088) }, { argument := 467424890035235184275619840, coefficient := (-467424890035235184275619840) }, { argument := 58860912078511097279152128, coefficient := (-58860912078511097279152128) }, { argument := 401639164771016899081273344, coefficient := (-401639164771016899081273344) }, { argument := 58860912078511097279152128, coefficient := (-58860912078511097279152128) }, { argument := 467424890035235184275619840, coefficient := (-467424890035235184275619840) }, { argument := 467424890035235184275619840, coefficient := (-467424890035235184275619840) }, { argument := 173563205699477843633766400, coefficient := (-173563205699477843633766400) }, { argument := 114724251023125407753830400, coefficient := (-114724251023125407753830400) }, { argument := 4689427143900873965436928000, coefficient := (-4689427143900873965436928000) }, { argument := 4689422958811293366301491200, coefficient := (-4689422958811293366301491200) }, { argument := 114717775138187849876111360, coefficient := (-114717775138187849876111360) }, { argument := 170988210049367164044967936, coefficient := (-170988210049367164044967936) }, { argument := 615096713676855585055703040, coefficient := (-615096713676855585055703040) }, { argument := 170968757158071028487815168, coefficient := (-170968757158071028487815168) }, { argument := 615096713676855585055703040, coefficient := (-615096713676855585055703040) }, { argument := 16055210118667150688130170880, coefficient := (-16055210118667150688130170880) }, { argument := 1688847206238632395038261248, coefficient := (-1688847206238632395038261248) }, { argument := 174357567875189069732774936576, coefficient := (-174357567875189069732774936576) }, { argument := 1440487322968245278120869888, coefficient := (-1440487322968245278120869888) }, { argument := 211105900779829049379782656, coefficient := (-211105900779829049379782656) }, { argument := 1676429212075113039192391680, coefficient := (-1676429212075113039192391680) }, { argument := 1676429212075113039192391680, coefficient := (-1676429212075113039192391680) }, { argument := 1440487322968245278120869888, coefficient := (-1440487322968245278120869888) }, { argument := 30436503694785941178226311168, coefficient := (-30436503694785941178226311168) }, { argument := 1440487322968245278120869888, coefficient := (-1440487322968245278120869888) }, { argument := 16055466337540186168518246400, coefficient := (-16055466337540186168518246400) }, { argument := 1676429212075113039192391680, coefficient := (-1676429212075113039192391680) }, { argument := 211105900779829049379782656, coefficient := (-211105900779829049379782656) }, { argument := 1440487322968245278120869888, coefficient := (-1440487322968245278120869888) }, { argument := 211105900779829049379782656, coefficient := (-211105900779829049379782656) }, { argument := 1676429212075113039192391680, coefficient := (-1676429212075113039192391680) }, { argument := 1676429212075113039192391680, coefficient := (-1676429212075113039192391680) }, { argument := 624977955515024919433838592, coefficient := (-624977955515024919433838592) }, { argument := 4689427143900873965436928000, coefficient := (-4689427143900873965436928000) }, { argument := 188577229148071457058088550400, coefficient := (-188577229148071457058088550400) }, { argument := 188577079856213752646782156800, coefficient := (-188577079856213752646782156800) }, { argument := 4689185695413167627886919680, coefficient := (-4689185695413167627886919680) }, { argument := 4461743124148371205323227136, coefficient := (-4461743124148371205323227136) }, { argument := 16055210118667150688130170880, coefficient := (-16055210118667150688130170880) }, { argument := 4461059795026892535348854784, coefficient := (-4461059795026892535348854784) }, { argument := 470887296628088778233217024, coefficient := (-470887296628088778233217024) }, { argument := 1688847206238632395038261248, coefficient := (-1688847206238632395038261248) }, { argument := 470888080614711910889160704, coefficient := (-470888080614711910889160704) }, { argument := 170968757158071028487815168, coefficient := (-170968757158071028487815168) }, { argument := 4461059795026892535348854784, coefficient := (-4461059795026892535348854784) }, { argument := 470888080614711910889160704, coefficient := (-470888080614711910889160704) }, { argument := 48415811777394828291222798336, coefficient := (-48415811777394828291222798336) }, { argument := 401639833465489571052519424, coefficient := (-401639833465489571052519424) }, { argument := 58861010076838988861145088, coefficient := (-58861010076838988861145088) }, { argument := 467425668257250793897328640, coefficient := (-467425668257250793897328640) }, { argument := 467425668257250793897328640, coefficient := (-467425668257250793897328640) }, { argument := 401639833465489571052519424, coefficient := (-401639833465489571052519424) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-39300802120063811508332742574080)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1840188741, 21772939, 15849126021737, 101356785, 12763447, 21772939,
    12763447, 101356785, 101356785, 154137868855, 8330088545725, 669960371113425,
    83744980090275, 16659319294365, 2688075409855, 619442516392571, 172007516771781, 87091611,
    312355897, 21772939, 51053703, 183105181, 12763447, 405426465,
    1454070555, 101356785, 405426465, 1454070555, 101356785, 87091611,
    312355897, 21772939, 7360742709, 26399458743, 1840188741, 87091611,
    312355897, 21772939, 407559408935, 8329667081265, 16659319294365, 203768201325,
    15851553753523, 14260118719225, 15849126021737, 405426465, 1454070555, 101356785,
    51053703, 183105181, 12763447, 87091611, 312355897, 21772939,
    51053703, 183105181, 12763447, 405426465, 1454070555, 101356785,
    405426465, 1454070555, 101356785, 616620375025
  ]
def negativeCoefficients : Array ℕ := #[
    8486372688137197746980388864, 401639833465489571052519424, 4461132377852674055415529472, 467425668257250793897328640, 58861010076838988861145088, 401639833465489571052519424,
    58861010076838988861145088, 467425668257250793897328640, 467425668257250793897328640, 173543812184765095236075520, 4689422958811293366301491200, 188577079856213752646782156800,
    188576930564356048235475763200, 4689181510396770522696253440, 48424061656667085244538552320, 174357567875189069732774936576, 48415811777394828291222798336, 401639164771016899081273344,
    1440487322968245278120869888, 401639833465489571052519424, 58860912078511097279152128, 211105900779829049379782656, 58861010076838988861145088, 467424890035235184275619840,
    1676429212075113039192391680, 467425668257250793897328640, 467424890035235184275619840, 1676429212075113039192391680, 467425668257250793897328640, 401639164771016899081273344,
    1440487322968245278120869888, 401639833465489571052519424, 8486358559084158790070697984, 30436503694785941178226311168, 8486372688137197746980388864, 401639164771016899081273344,
    1440487322968245278120869888, 401639833465489571052519424, 114717775138187849876111360, 4689185695413167627886919680, 4689181510396770522696253440, 114711299444653276161638400,
    4461815723600598124711641088, 16055466337540186168518246400, 4461132377852674055415529472, 467424890035235184275619840, 1676429212075113039192391680, 467425668257250793897328640,
    58860912078511097279152128, 211105900779829049379782656, 58861010076838988861145088, 401639164771016899081273344, 1440487322968245278120869888, 401639833465489571052519424,
    58860912078511097279152128, 211105900779829049379782656, 58861010076838988861145088, 467424890035235184275619840, 1676429212075113039192391680, 467425668257250793897328640,
    467424890035235184275619840, 1676429212075113039192391680, 467425668257250793897328640, 173563205699477843633766400
  ]
def negativeScales : Array ℕ := #[
    30, 24, 43, 26, 23, 24,
    23, 26, 26, 37, 42, 49,
    46, 43, 41, 49, 47, 26,
    28, 24, 25, 27, 23, 28,
    30, 26, 28, 30, 26, 26,
    28, 24, 32, 34, 30, 26,
    28, 24, 38, 42, 43, 37,
    43, 43, 43, 28, 30, 26,
    25, 27, 23, 26, 28, 24,
    25, 27, 23, 28, 30, 26,
    28, 30, 26, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30777206599878083, 24376032825735850, 43849468522374012, 26594867427664009, 23605514671865197, 24376032825735850,
    23605514671865197, 26594867427664009, 26594867427664009, 37165430392943814, 42921468976015399, 49251069089532276,
    46251067947385477, 43921394692795477, 41289710749941291, 49137963736433470, 47289464940864498, 26376030423775381,
    28218615526051623, 24376032825735850, 25605512269904727, 27448097372174434, 23605514671865197, 28594865025703540,
    30437450127974911, 26594867427664009, 28594865025703540, 30437450127974911, 26594867427664009, 26376030423775381,
    28218615526051623, 24376032825735850, 32777204197917594, 34619789299800578, 30777206599878083, 26376030423775381,
    28218615526051623, 24376032825735850, 38568219416551927, 42921395980376341, 43921394692795477, 37568137975688612,
    43849689494085337, 43697051226249288, 43849468522374012, 28594865025703540, 30437450127974911, 26594867427664009,
    25605512269904727, 27448097372174434, 23605514671865197, 26376030423775381, 28218615526051623, 24376032825735850,
    25605512269904727, 27448097372174434, 23605514671865197, 28594865025703540, 30437450127974911, 26594867427664009,
    28594865025703540, 30437450127974911, 26594867427664009, 39165591605054713
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
noncomputable def negativeCeiling : ℝ := 428027887 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8486372688137197746980388864, coefficient := (-8486372688137197746980388864) }, { argument := 401639833465489571052519424, coefficient := (-401639833465489571052519424) }, { argument := 4461132377852674055415529472, coefficient := (-4461132377852674055415529472) }, { argument := 467425668257250793897328640, coefficient := (-467425668257250793897328640) }, { argument := 58861010076838988861145088, coefficient := (-58861010076838988861145088) }, { argument := 401639833465489571052519424, coefficient := (-401639833465489571052519424) }, { argument := 58861010076838988861145088, coefficient := (-58861010076838988861145088) }, { argument := 467425668257250793897328640, coefficient := (-467425668257250793897328640) }, { argument := 467425668257250793897328640, coefficient := (-467425668257250793897328640) }, { argument := 173543812184765095236075520, coefficient := (-173543812184765095236075520) }, { argument := 4689422958811293366301491200, coefficient := (-4689422958811293366301491200) }, { argument := 188577079856213752646782156800, coefficient := (-188577079856213752646782156800) }, { argument := 188576930564356048235475763200, coefficient := (-188576930564356048235475763200) }, { argument := 4689181510396770522696253440, coefficient := (-4689181510396770522696253440) }, { argument := 48424061656667085244538552320, coefficient := (-48424061656667085244538552320) }, { argument := 174357567875189069732774936576, coefficient := (-174357567875189069732774936576) }, { argument := 48415811777394828291222798336, coefficient := (-48415811777394828291222798336) }, { argument := 401639164771016899081273344, coefficient := (-401639164771016899081273344) }, { argument := 1440487322968245278120869888, coefficient := (-1440487322968245278120869888) }, { argument := 401639833465489571052519424, coefficient := (-401639833465489571052519424) }, { argument := 58860912078511097279152128, coefficient := (-58860912078511097279152128) }, { argument := 211105900779829049379782656, coefficient := (-211105900779829049379782656) }, { argument := 58861010076838988861145088, coefficient := (-58861010076838988861145088) }, { argument := 467424890035235184275619840, coefficient := (-467424890035235184275619840) }, { argument := 1676429212075113039192391680, coefficient := (-1676429212075113039192391680) }, { argument := 467425668257250793897328640, coefficient := (-467425668257250793897328640) }, { argument := 467424890035235184275619840, coefficient := (-467424890035235184275619840) }, { argument := 1676429212075113039192391680, coefficient := (-1676429212075113039192391680) }, { argument := 467425668257250793897328640, coefficient := (-467425668257250793897328640) }, { argument := 401639164771016899081273344, coefficient := (-401639164771016899081273344) }, { argument := 1440487322968245278120869888, coefficient := (-1440487322968245278120869888) }, { argument := 401639833465489571052519424, coefficient := (-401639833465489571052519424) }, { argument := 8486358559084158790070697984, coefficient := (-8486358559084158790070697984) }, { argument := 30436503694785941178226311168, coefficient := (-30436503694785941178226311168) }, { argument := 8486372688137197746980388864, coefficient := (-8486372688137197746980388864) }, { argument := 401639164771016899081273344, coefficient := (-401639164771016899081273344) }, { argument := 1440487322968245278120869888, coefficient := (-1440487322968245278120869888) }, { argument := 401639833465489571052519424, coefficient := (-401639833465489571052519424) }, { argument := 114717775138187849876111360, coefficient := (-114717775138187849876111360) }, { argument := 4689185695413167627886919680, coefficient := (-4689185695413167627886919680) }, { argument := 4689181510396770522696253440, coefficient := (-4689181510396770522696253440) }, { argument := 114711299444653276161638400, coefficient := (-114711299444653276161638400) }, { argument := 4461815723600598124711641088, coefficient := (-4461815723600598124711641088) }, { argument := 16055466337540186168518246400, coefficient := (-16055466337540186168518246400) }, { argument := 4461132377852674055415529472, coefficient := (-4461132377852674055415529472) }, { argument := 467424890035235184275619840, coefficient := (-467424890035235184275619840) }, { argument := 1676429212075113039192391680, coefficient := (-1676429212075113039192391680) }, { argument := 467425668257250793897328640, coefficient := (-467425668257250793897328640) }, { argument := 58860912078511097279152128, coefficient := (-58860912078511097279152128) }, { argument := 211105900779829049379782656, coefficient := (-211105900779829049379782656) }, { argument := 58861010076838988861145088, coefficient := (-58861010076838988861145088) }, { argument := 401639164771016899081273344, coefficient := (-401639164771016899081273344) }, { argument := 1440487322968245278120869888, coefficient := (-1440487322968245278120869888) }, { argument := 401639833465489571052519424, coefficient := (-401639833465489571052519424) }, { argument := 58860912078511097279152128, coefficient := (-58860912078511097279152128) }, { argument := 211105900779829049379782656, coefficient := (-211105900779829049379782656) }, { argument := 58861010076838988861145088, coefficient := (-58861010076838988861145088) }, { argument := 467424890035235184275619840, coefficient := (-467424890035235184275619840) }, { argument := 1676429212075113039192391680, coefficient := (-1676429212075113039192391680) }, { argument := 467425668257250793897328640, coefficient := (-467425668257250793897328640) }, { argument := 467424890035235184275619840, coefficient := (-467424890035235184275619840) }, { argument := 1676429212075113039192391680, coefficient := (-1676429212075113039192391680) }, { argument := 467425668257250793897328640, coefficient := (-467425668257250793897328640) }, { argument := 173563205699477843633766400, coefficient := (-173563205699477843633766400) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8
