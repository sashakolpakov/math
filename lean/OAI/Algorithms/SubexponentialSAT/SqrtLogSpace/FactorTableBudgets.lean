import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyPolynomial
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchBound

/-! Fixed polynomial bounds for the actual factor-table service. The scalar
allowance includes physical signed-word lengths; it never bounds the integer
value of an exponential modulus or numerator in unary. All ambient source
rows and every specialized incidence record are included. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open OAI.Algorithms.SubexponentialSAT.Subexp
open FactorTableNative

private theorem scalar_allowance_ordinary :
    Ordinary (fun S => LayoutSourceValuesProgram.Native.scalarAllowance S S S S S) := by
  unfold LayoutSourceValuesProgram.Native.scalarAllowance
    LayoutProgramScalar.FromCounts.binomialCost LayoutProgramScalar.numeratorPrepareCost
    LayoutProgramScalar.numeratorFoldCost LayoutProgramScalar.termGrowth
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 14) ordinary_id) (ordinary_mul (ordinary_const 7) ordinary_id)) (ordinary_const 15)) (ordinary_add (ordinary_mul (ordinary_const 3) ordinary_id) (ordinary_const 4))) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 12) ordinary_id) (ordinary_mul (ordinary_mul (ordinary_mul (ordinary_const 400) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add ordinary_id (ordinary_const 5)))) (ordinary_mul (ordinary_mul (ordinary_const 110) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add (ordinary_add ordinary_id (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_const 4)))) (ordinary_const 32))) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 9) ordinary_id) (ordinary_mul (ordinary_const 3) ordinary_id)) (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 28) ordinary_id) (ordinary_const 34))) (ordinary_mul (ordinary_const 140) ordinary_id)) (ordinary_mul (ordinary_const 18) ordinary_id)) (ordinary_const 222)))) (ordinary_mul (ordinary_const 3) (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 8) ordinary_id) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 9))))) (ordinary_const 24)) (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 200000000) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_pow (ordinary_add (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_const 52))) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_const 4)) 2)) (ordinary_const 1))) (ordinary_const 1))) (ordinary_mul (ordinary_const 4) (ordinary_mul ordinary_id ordinary_id))) (ordinary_const 6)) (ordinary_const 1))

private theorem numerator_allowance_ordinary :
    Ordinary (fun S => LayoutSourceValuesProgram.Native.numeratorAllowance S S S S S S) := by
  unfold LayoutSourceValuesProgram.Native.numeratorAllowance
    MatrixExtendedEntryProgram.guardStageCost MatrixEntryProgram.scanStageCost
    CollisionProgram.typeWidth
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 36) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_mul ordinary_id ordinary_id)) (ordinary_const 17)))) (ordinary_mul (ordinary_const 203) (ordinary_mul ordinary_id ordinary_id))) (ordinary_const 265)) (ordinary_add (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 9) (ordinary_mul ordinary_id ordinary_id)) (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 14) ordinary_id) (ordinary_const 17)))) (ordinary_mul (ordinary_const 30) ordinary_id)) (ordinary_const 43))) (ordinary_const 1))) (ordinary_add (ordinary_mul (ordinary_const 81) ordinary_id) (ordinary_const 107))) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 8) (ordinary_mul ordinary_id ordinary_id)) (ordinary_mul (ordinary_const 8) ordinary_id)) (ordinary_const 24))) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 5)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 36) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_mul ordinary_id ordinary_id)) (ordinary_const 17)))) (ordinary_mul (ordinary_const 203) (ordinary_mul ordinary_id ordinary_id))) (ordinary_const 265))) (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 208) ordinary_id) (ordinary_const 149))) (ordinary_const 3)))) (ordinary_mul (ordinary_const 7) ordinary_id)) scalar_allowance_ordinary) (ordinary_const 20))

private theorem value_table_ordinary :
    Ordinary (fun S => LayoutSourceValuesProgram.Native.polynomialBudget S S S S S S S S) := by
  unfold LayoutSourceValuesProgram.Native.polynomialBudget
    LayoutSourceValuesProgram.Native.callbackBudget
    LayoutSourceValuesProgram.Native.integerBits IntegerRingLiftProgram.polynomialBudget
    LayoutProgramScalar.termGrowth
  simp only [RingProgram.ternary_baseWidth]
  exact (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul ordinary_id numerator_allowance_ordinary) (ordinary_const 1)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_const 52))) (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 100000) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 3)) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 2)) (ordinary_mul (ordinary_mul (ordinary_const 80) ordinary_id) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_const 110))) (ordinary_mul (ordinary_mul (ordinary_const 200000) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 3)) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 2))) (ordinary_mul (ordinary_mul (ordinary_const 203) ordinary_id) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_const 251))) (ordinary_mul (ordinary_const 2) (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_const 52))))) (ordinary_const 6)) (ordinary_mul (ordinary_const 6) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_const 16))) (ordinary_const 14))

private theorem value_table_le {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S : ℕ)
    (hr : r ≤ S) (hQ : Q ≤ S) (hd : d ≤ S) (ht : p.t ≤ S)
    (hR : p.R ≤ S) (hA : p.aWord.length ≤ S) (hW : p.width.length ≤ S)
    (hP : RowSelectionProgram.pairLength p.power ≤ S) :
    LayoutSourceValuesProgram.Native.polynomialBudget r Q p.aWord.length p.R
      p.width.length (RowSelectionProgram.pairLength p.power) p.t d ≤
    LayoutSourceValuesProgram.Native.polynomialBudget S S S S S S S S := by
  unfold LayoutSourceValuesProgram.Native.polynomialBudget
    LayoutSourceValuesProgram.Native.callbackBudget
    LayoutSourceValuesProgram.Native.integerBits IntegerRingLiftProgram.polynomialBudget
    LayoutSourceValuesProgram.Native.numeratorAllowance
    LayoutSourceValuesProgram.Native.scalarAllowance
    LayoutProgramScalar.FromCounts.binomialCost LayoutProgramScalar.numeratorPrepareCost
    LayoutProgramScalar.numeratorFoldCost LayoutProgramScalar.termGrowth
    MatrixExtendedEntryProgram.guardStageCost MatrixEntryProgram.scanStageCost
    CollisionProgram.typeWidth
  simp only [RingProgram.ternary_baseWidth]
  gcongr

private theorem source_bound_mono : Monotone UniversalRowSourceBound.sourceBound := by
  intro S T h
  unfold UniversalRowSourceBound.sourceBound UniversalRowSourceBound.dataBound
    UniversalRowSourceBound.outerLoopBound UniversalRowSourceBound.termBound
    UniversalRowSourceBound.factorLoopBound UniversalRowSourceBound.factorCallbackBound
    UniversalRowSourceBound.inputBound UniversalRowSourceBound.rowBytes
    UniversalRowSourceBound.termBytes UniversalRowSourceBound.factorsBytes
    UniversalRowSourceBound.factorBytes UniversalRowSourceBound.indicesBound
  gcongr

private theorem source_bound_ordinary {f : ℕ → ℕ} (hf : Ordinary f) :
    Ordinary (fun S => UniversalRowSourceBound.sourceBound (f S)) := by
  unfold UniversalRowSourceBound.sourceBound UniversalRowSourceBound.dataBound
    UniversalRowSourceBound.outerLoopBound UniversalRowSourceBound.termBound
    UniversalRowSourceBound.factorLoopBound UniversalRowSourceBound.factorCallbackBound
    UniversalRowSourceBound.inputBound UniversalRowSourceBound.rowBytes
    UniversalRowSourceBound.termBytes UniversalRowSourceBound.factorsBytes
    UniversalRowSourceBound.factorBytes UniversalRowSourceBound.indicesBound
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 10) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 2)) hf))) (ordinary_mul (ordinary_const 13) hf)) (ordinary_mul (ordinary_const 6) hf)) (ordinary_const 40)) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 2)) hf))) (ordinary_const 8)) (ordinary_mul hf (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 6) hf) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul hf (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 28) hf) (ordinary_mul (ordinary_const 14) hf)) (ordinary_const 51))) (ordinary_mul (ordinary_const 30) hf)) (ordinary_mul (ordinary_const 15) hf)) (ordinary_const 63)) (ordinary_mul (ordinary_const 7) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 2)) hf)))) (ordinary_mul hf (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 6) hf) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 28) hf) (ordinary_const 60)) hf) (ordinary_mul (ordinary_const 9) hf)) (ordinary_mul (ordinary_const 80) hf)) (ordinary_const 140))) (ordinary_const 7)))) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 24) (ordinary_add hf hf)) (ordinary_mul (ordinary_const 8) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_const 4) hf) (ordinary_const 2))) (ordinary_const 2)) hf)))) (ordinary_const 42))) (ordinary_mul (ordinary_const 2) hf)) (ordinary_mul (ordinary_const 2) hf)) (ordinary_const 20))) (ordinary_const 7))))) (ordinary_mul (ordinary_const 8) hf)) (ordinary_const 11)) (ordinary_mul (ordinary_const 2048) (ordinary_pow (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 2)) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 4) hf) (ordinary_const 2)) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_const 4) hf) (ordinary_const 2))) (ordinary_const 2)) hf)))) (ordinary_const 2)) hf))) (ordinary_const 1)) 2))) (ordinary_const 4))

private theorem source_length_ordinary : Ordinary UniversalRowSourceBound.sourceLengthBound := by
  unfold UniversalRowSourceBound.sourceLengthBound UniversalRowSourceBound.inputBound
    UniversalRowSourceBound.rowBytes UniversalRowSourceBound.termBytes
    UniversalRowSourceBound.factorsBytes UniversalRowSourceBound.factorBytes
  exact (ordinary_mul (ordinary_const 300) (ordinary_pow (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 2)) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 4) ordinary_id) (ordinary_const 2)) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_const 4) ordinary_id) (ordinary_const 2))) (ordinary_const 2)) ordinary_id)))) (ordinary_const 2)) ordinary_id))) (ordinary_const 1)) 2))

def workspaceEnvelope (S : ℕ) : ℕ :=
  S+S*(S*(2*S))+UniversalRowSourceBound.indicesBound S

def uniformEnvelope (S : ℕ) : ℕ :=
  LayoutSourceValuesProgram.Native.polynomialBudget S S S S S S S S +
    (UniversalRowMismatchTypes.extractBudget (r := S) (Q := S) (0 : Fin 1)+
      UniversalRowMismatchBound.mismatchBound (S+1)+8*(S*S)+13)+
    14*S+224*workspaceEnvelope S+UniversalRowSourceBound.sourceBound (workspaceEnvelope S)+281

private theorem workspace_ordinary : Ordinary workspaceEnvelope := by
  unfold workspaceEnvelope UniversalRowSourceBound.indicesBound
  exact (ordinary_add (ordinary_add ordinary_id (ordinary_mul ordinary_id (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 2)) ordinary_id)))

private theorem uniform_ordinary : Ordinary uniformEnvelope := by
  unfold uniformEnvelope UniversalRowMismatchTypes.extractBudget
    UniversalRowMismatchBound.mismatchBound CollisionProgram.typeWidth
  simp only [Fin.val_zero, Nat.zero_add]
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add value_table_ordinary (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 36) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_mul ordinary_id ordinary_id)) (ordinary_const 17)))) (ordinary_mul (ordinary_const 203) (ordinary_mul ordinary_id ordinary_id))) (ordinary_const 265)) (ordinary_mul (ordinary_const 400) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 3))) (ordinary_mul (ordinary_const 8) (ordinary_mul ordinary_id ordinary_id))) (ordinary_const 13))) (ordinary_mul (ordinary_const 14) ordinary_id)) (ordinary_mul (ordinary_const 224) workspace_ordinary)) (source_bound_ordinary workspace_ordinary)) (ordinary_const 281))

private theorem uniform_le {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (E S : ℕ)
    (hE : E ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hd : d ≤ S) (ht : p.t ≤ S)
    (hR : p.R ≤ S) (hA : p.aWord.length ≤ S) (hW : p.width.length ≤ S)
    (hP : RowSelectionProgram.pairLength p.power ≤ S) :
    SourceBank.uniformBudget p E ≤ uniformEnvelope S := by
  have hv := value_table_le p S hr hQ hd ht hR hA hW hP
  have hm := UniversalRowMismatchBound.budget_le Q r (S+1) (by omega)
    (by omega) (by omega)
  have he : UniversalRowMismatchTypes.extractBudget (r := r) (Q := Q) (0 : Fin 1) ≤
      UniversalRowMismatchTypes.extractBudget (r := S) (Q := S) (0 : Fin 1) := by
    unfold UniversalRowMismatchTypes.extractBudget CollisionProgram.typeWidth
    gcongr
  have hw : SourceBank.sourceWorkspace p E ≤ workspaceEnvelope S := by
    unfold SourceBank.sourceWorkspace workspaceEnvelope UniversalRowSourceBound.indicesBound
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  have hs := source_bound_mono hw
  unfold SourceBank.uniformBudget uniformEnvelope
  gcongr

/-- State-independent allowance for every actual ambient source row. -/
def sourceEnvelope (S : ℕ) : ℕ :=
  let B := 2*S
  let W := (S+1)*(S*B)
  let K := 800*(2*S+1)^2+uniformEnvelope S+200*S+302+12*S+12
  LayoutSourceRowsProgramInitialize.budget (S+1) (S*B)+1000*(4*S+1)^2+
    S*(rowBudgetPolynomial K (UniversalRowSourceBound.sourceLengthBound S)
      (S+1) S B S+45*W+83)+2*S+23+
    1000000000000*(S+(67108864*S+1+W+(S+1)+S*(2*W+2)+1)+1)

private theorem source_envelope_ordinary : Ordinary sourceEnvelope := by
  unfold sourceEnvelope LayoutSourceRowsProgramInitialize.budget rowBudgetPolynomial
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 240) (ordinary_add (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_const 1))) (ordinary_add (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 1))) (ordinary_mul (ordinary_const 1000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 4) ordinary_id) (ordinary_const 1)) 2))) (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 1000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 2)) (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 800) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 2)) uniform_ordinary) (ordinary_mul (ordinary_const 200) ordinary_id)) (ordinary_const 302)) (ordinary_mul (ordinary_const 12) ordinary_id)) (ordinary_const 12)) (ordinary_mul (ordinary_const 5) ordinary_id)) (ordinary_mul (ordinary_const 3) source_length_ordinary)) (ordinary_const 15)))) (ordinary_mul (ordinary_mul (ordinary_mul (ordinary_mul (ordinary_const 300000) (ordinary_add (ordinary_add (ordinary_const 2) (ordinary_mul ordinary_id (ordinary_add source_length_ordinary (ordinary_const 2)))) (ordinary_const 1))) (ordinary_pow (ordinary_add (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_const 1)) 3)) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 3)) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 2))) (ordinary_mul (ordinary_const 18) (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id))))) (ordinary_mul (ordinary_const 12) ordinary_id)) (ordinary_mul (ordinary_const 3) (ordinary_add (ordinary_const 2) (ordinary_mul ordinary_id (ordinary_add source_length_ordinary (ordinary_const 2)))))) (ordinary_const 67)) (ordinary_mul (ordinary_const 45) (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id))))) (ordinary_const 83)))) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 23)) (ordinary_mul (ordinary_const 1000000000000) (ordinary_add (ordinary_add ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 67108864) ordinary_id) (ordinary_const 1)) (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_const 2)))) (ordinary_const 1))) (ordinary_const 1))))

theorem source_work_le {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (E S : ℕ)
    (hE : E ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hd : d ≤ S) (ht : p.t ≤ S)
    (hR : p.R ≤ S) (hA : p.aWord.length ≤ S) (hW : p.width.length ≤ S)
    (hP : RowSelectionProgram.pairLength p.power ≤ S) :
    LeafProgram.Source.nativeSourceWorkPolynomial p E ≤ sourceEnvelope S := by
  have hu := uniform_le p E S hE hr hQ hd ht hR hA hW hP
  have hl : UniversalRowSourceBound.sourceLengthBound E ≤
      UniversalRowSourceBound.sourceLengthBound S := by
    unfold UniversalRowSourceBound.sourceLengthBound UniversalRowSourceBound.inputBound
      UniversalRowSourceBound.rowBytes UniversalRowSourceBound.termBytes
      UniversalRowSourceBound.factorsBytes UniversalRowSourceBound.factorBytes
    gcongr
  unfold LeafProgram.Source.nativeSourceWorkPolynomial nativeRowsPolynomial
    stagedSourceBudget nativeSourceBudget LeafProgram.Source.nativeOutputBound sourceEnvelope
    LayoutSourceRowsProgramInitialize.budget rowBudgetPolynomial
  simp only [RingProgram.ternary_baseWidth]
  gcongr

/-- Constants and degree precede every runtime source parameter and word. -/
theorem source_work_polynomial : ∃ C e : ℕ, ∀ {r Q d : ℕ}
    (p : SourceBank.Parameters r Q d) (E S : ℕ),
    E ≤ S → r ≤ S → Q ≤ S → d ≤ S → p.t ≤ S → p.R ≤ S →
    p.aWord.length ≤ S → p.width.length ≤ S → RowSelectionProgram.pairLength p.power ≤ S →
    LeafProgram.Source.nativeSourceWorkPolynomial p E ≤ C*(S+1)^e := by
  obtain ⟨C,e,hpoly⟩ := source_envelope_ordinary
  exact ⟨C,e,fun p E S hE hr hQ hd ht hR hA hW hP =>
    (source_work_le p E S hE hr hQ hd ht hR hA hW hP).trans (hpoly S)⟩

/-- Full normalized payload width, before inserting its framed table record. -/
def payloadEnvelope (S : ℕ) : ℕ := S*S*(2*(S+S+S)+2*S*(2*S)+2)

def specializationEnvelope (S : ℕ) : ℕ :=
  (3200000*(1000000000*3^10+64)^10)*(10*(S+1))^100

def literalEnvelope (S : ℕ) : ℕ :=
  7*S+(10*S+9*S+18+(10*S+42*S+29*(S*(2*S))+109)+
    (sourceEnvelope S+1+(7*S+5+specializationEnvelope S)))+
    22*(S+1)+19*payloadEnvelope S+
    2*(S*(2*((S+1)*(S*(2*S)))+2)+1)+54

/-- Includes the complete ambient loop, its growing table and export cleanup. -/
def tableEnvelope (S : ℕ) : ℕ :=
  1000000*(S+S+literalEnvelope S+payloadEnvelope S+1)^2

/-- A local prefix allowance and compact retained table allowance together.
This is a fixed polynomial in scalar and physical-word caps, not total query time. -/
def serviceEnvelope (S : ℕ) : ℕ :=
  896*S+tableEnvelope S+1+S*FactorTableProgram.literalRecordBound S (payloadEnvelope S)

theorem payload_bound_le (n u J t d S : ℕ)
    (hn : n ≤ S) (hu : u ≤ S) (hJ : J ≤ S) (ht : t ≤ S) (hd : d ≤ S) :
    specializedPayloadBound n u J (baseWidth 3 t) d ≤ payloadEnvelope S := by
  unfold specializedPayloadBound payloadEnvelope
  simp only [RingProgram.ternary_baseWidth]
  rw [← Nat.mul_assoc 2 d (2*t)]
  gcongr

theorem specialization_work_le (t d u J R n E S : ℕ)
    (ht : t ≤ S) (hd : d ≤ S) (hu : u ≤ S) (hJ : J ≤ S)
    (hR : R ≤ S) (hn : n ≤ S) (hE : E ≤ S) :
    specializedWorkPolynomial t d u J (R+1) n E ≤ specializationEnvelope S := by
  apply (specializedWorkPolynomial_bound t d u J (R+1) n E).trans
  unfold specializationEnvelope
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp only [RingProgram.ternary_baseWidth]
  omega

theorem literal_work_le {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (u J n E H S : ℕ) (hu : u ≤ S) (hJ : J ≤ S) (hn : n ≤ S) (hE : E ≤ S)
    (hH : H ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hd : d ≤ S) (ht : p.t ≤ S)
    (hR : p.R ≤ S) (hA : p.aWord.length ≤ S) (hW : p.width.length ≤ S)
    (hP : RowSelectionProgram.pairLength p.power ≤ S) :
    specializedLiteralWork p u J n E H ≤ literalEnvelope S := by
  have hsource := source_work_le p E S hE hr hQ hd ht hR hA hW hP
  have hspecial := specialization_work_le p.t d u J p.R n E S ht hd hu hJ hR hn hE
  have hpayload := payload_bound_le n u J p.t d S hn hu hJ ht hd
  unfold specializedLiteralWork literalEnvelope
  simp only [RingProgram.ternary_baseWidth] at hpayload ⊢
  gcongr

theorem command_budget_le {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (u J n E H B S : ℕ) (hu : u ≤ S) (hJ : J ≤ S) (hn : n ≤ S) (hE : E ≤ S)
    (hH : H ≤ S) (hB : B ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hd : d ≤ S)
    (ht : p.t ≤ S) (hR : p.R ≤ S) (hA : p.aWord.length ≤ S)
    (hW : p.width.length ≤ S) (hP : RowSelectionProgram.pairLength p.power ≤ S) :
    FactorTableSpace.commandBudget B n (specializedLiteralWork p u J n E H)
      (specializedPayloadBound n u J (baseWidth 3 p.t) d) ≤ tableEnvelope S := by
  apply FactorTableSpace.commandBudget_le .. |>.trans
  unfold tableEnvelope
  have hl := literal_work_le p u J n E H S hu hJ hn hE hH hr hQ hd ht hR hA hW hP
  have hp := payload_bound_le n u J p.t d S hn hu hJ ht hd
  gcongr

private theorem payload_ordinary : Ordinary payloadEnvelope := by
  unfold payloadEnvelope
  exact (ordinary_mul (ordinary_mul ordinary_id ordinary_id) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add ordinary_id ordinary_id) ordinary_id)) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_const 2)))

private theorem specialization_ordinary : Ordinary specializationEnvelope := by
  unfold specializationEnvelope
  exact (ordinary_mul (ordinary_const (3200000*(1000000000*3^10+64)^10)) (ordinary_pow (ordinary_mul (ordinary_const 10) (ordinary_add ordinary_id (ordinary_const 1))) 100))

private theorem literal_ordinary : Ordinary literalEnvelope := by
  unfold literalEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 10) ordinary_id) (ordinary_mul (ordinary_const 9) ordinary_id)) (ordinary_const 18)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 10) ordinary_id) (ordinary_mul (ordinary_const 42) ordinary_id)) (ordinary_mul (ordinary_const 29) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_const 109))) (ordinary_add (ordinary_add source_envelope_ordinary (ordinary_const 1)) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 5)) specialization_ordinary)))) (ordinary_mul (ordinary_const 22) (ordinary_add ordinary_id (ordinary_const 1)))) (ordinary_mul (ordinary_const 19) payload_ordinary)) (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_const 2))) (ordinary_const 1)))) (ordinary_const 54))

private theorem table_ordinary : Ordinary tableEnvelope := by
  unfold tableEnvelope
  exact (ordinary_mul (ordinary_const 1000000) (ordinary_pow (ordinary_add (ordinary_add (ordinary_add (ordinary_add ordinary_id ordinary_id) literal_ordinary) payload_ordinary) (ordinary_const 1)) 2))

private theorem service_ordinary : Ordinary serviceEnvelope := by
  unfold serviceEnvelope FactorTableProgram.literalRecordBound
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 896) ordinary_id) table_ordinary) (ordinary_const 1)) (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_mul (ordinary_const 2) payload_ordinary)) (ordinary_const 4))))

/-- The same fixed coefficient and exponent bound the actual table call time,
its all-stack prefix allowance and the full compact table retained at return. -/
theorem table_service_polynomial : ∃ C e : ℕ, ∀ {r Q d : ℕ}
    (p : SourceBank.Parameters r Q d) (u J n E H B S : ℕ),
    u ≤ S → J ≤ S → n ≤ S → E ≤ S → H ≤ S → B ≤ S → r ≤ S → Q ≤ S →
    d ≤ S → p.t ≤ S → p.R ≤ S → p.aWord.length ≤ S → p.width.length ≤ S →
    RowSelectionProgram.pairLength p.power ≤ S →
    let K := specializedLiteralWork p u J n E H
    let L := specializedPayloadBound n u J (baseWidth 3 p.t) d
    FactorTableSpace.commandBudget B n K L ≤ C*(S+1)^e ∧
    896*B+FactorTableSpace.commandBudget B n K L+1 ≤ C*(S+1)^e ∧
    n*FactorTableProgram.literalRecordBound n L ≤ C*(S+1)^e := by
  obtain ⟨C,e,hpoly⟩ := service_ordinary
  refine ⟨C,e,?_⟩
  intro r Q d p u J n E H B S hu hJ hn hE hH hB hr hQ hd ht hR hA hW hP
  dsimp only
  have hc := command_budget_le p u J n E H B S hu hJ hn hE hH hB hr hQ hd ht hR hA hW hP
  have hp := payload_bound_le n u J p.t d S hn hu hJ ht hd
  have htape : n*FactorTableProgram.literalRecordBound n
      (specializedPayloadBound n u J (baseWidth 3 p.t) d) ≤
      S*FactorTableProgram.literalRecordBound S (payloadEnvelope S) := by
    unfold FactorTableProgram.literalRecordBound
    gcongr
  have hprefix : 896*B+FactorTableSpace.commandBudget B n
      (specializedLiteralWork p u J n E H)
      (specializedPayloadBound n u J (baseWidth 3 p.t) d)+1 ≤ serviceEnvelope S := by
    unfold serviceEnvelope
    have := Nat.mul_le_mul_left 896 hB
    omega
  exact ⟨(by omega : FactorTableSpace.commandBudget B n
      (specializedLiteralWork p u J n E H)
      (specializedPayloadBound n u J (baseWidth 3 p.t) d) ≤ serviceEnvelope S).trans (hpoly S),
    hprefix.trans (hpoly S), htape.trans (by unfold serviceEnvelope; omega) |>.trans (hpoly S)⟩

/-- Public fixed-polynomial certificates for composing physical caps. -/
theorem payloadEnvelope_polynomial : Ordinary payloadEnvelope := payload_ordinary

theorem tableEnvelope_polynomial : Ordinary tableEnvelope := table_ordinary

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
