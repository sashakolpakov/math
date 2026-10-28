import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramExpansionFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramMeaning
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramOrigin
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyEncoding

namespace OAI.Algorithms

/-! Exact bytes and coefficient meaning at the raw-row/interpreter boundary.
The full extension dimension is D; the assembler parameter is D-1. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Expansion
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open HashCircuitProgram.Native
attribute [local simp] Fin.coe_ofNat_eq_mod

def coefficient (t : ℕ) : (D : ℕ) → ZMod 3 → RingProgram.Code (RingProgram.ScalarCode 3 t) D
  | 0, _ => Fin.elim0
  | d+1, c => constantVector t d c

theorem coefficient_flat (t D : ℕ) (hD : 0 < D) (c : ZMod 3) :
    RingProgram.flat (coefficient t D c)=RingProgram.flat (constantVector t (D-1) c) := by
  cases D with
  | zero => omega
  | succ d => rfl

theorem coefficient_decode (t D : ℕ) (ht : 0 < t) (hD : 0 < D)
    (model : RingModel.Data D) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (c : ZMod 3) :
    (RingProgram.modelRing t ht hD model M cache).decode (coefficient t D c)=
      LeafProgram.TernaryLift.coefficient model t c := by
  cases D with
  | zero => omega
  | succ d => exact constantVector_decode t d ht model M cache c

def encodedClauses {n : ℕ} (source : List (List (SAT.Literal (Fin n)))) : List (List Bool) :=
  source.map clausePayload

def originalClause {n : ℕ} (source : List (List (SAT.Literal (Fin n))))
    (i : Fin (encodedClauses source).length) : List (SAT.Literal (Fin n)) :=
  source[i.val]'(by simpa [encodedClauses] using i.isLt)

def weightedClause {n : ℕ} (t D : ℕ) (source : List (List (SAT.Literal (Fin n))))
    (term : Fin (encodedClauses source).length × ZMod 3) :
    Row.WeightedClause n (SubexpLiftRing.baseWidth 3 t) D :=
  ⟨coefficient t D term.2,originalClause source term.1⟩

def weightedRow {n : ℕ} (t D : ℕ) (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (encodedClauses source).length × ZMod 3)) :
    List (Row.WeightedClause n (SubexpLiftRing.baseWidth 3 t) D) :=
  terms.map (weightedClause t D source)

theorem weightedClause_payload {n : ℕ} (t D : ℕ) (hD : 0 < D)
    (source : List (List (SAT.Literal (Fin n))))
    (term : Fin (encodedClauses source).length × ZMod 3) :
    Row.payload (weightedClause t D source term)=
      Loop.payload t (D-1) (encodedClauses source) term := by
  rw [Row.payload,Row.literalList_eq]
  simp only [weightedClause,coefficient_flat t D hD]
  rw [← clausePayload_codes]
  simp [Loop.payload,encodedClauses,originalClause]

/-- Exact serialized bytes, with every zero, repeated clause, and repeated
literal retained in original tuple order. -/
theorem outputWord_eq {n : ℕ} (t D : ℕ) (hD : 0 < D)
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (encodedClauses source).length × ZMod 3)) :
    LeafProgram.Expansion.outputWord t (D-1) (encodedClauses source) terms=
      Encoding.encodeList id ((weightedRow t D source terms).map Row.payload) := by
  unfold LeafProgram.Expansion.outputWord weightedRow
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro term _
  exact (weightedClause_payload t D hD source term).symm

@[simp] theorem weightedRow_length {n : ℕ} (t D : ℕ)
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (encodedClauses source).length × ZMod 3)) :
    (weightedRow t D source terms).length=terms.length := by simp [weightedRow]

theorem weightedRow_decode {n : ℕ} (t D : ℕ) (ht : 0 < t) (hD : 0 < D)
    (model : RingModel.Data D) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (encodedClauses source).length × ZMod 3)) :
    (weightedRow t D source terms).map
      (fun w => ((RingProgram.modelRing t ht hD model M cache).decode w.scalar,w.literals))=
      terms.map (fun term => (LeafProgram.TernaryLift.coefficient model t term.2,
        originalClause source term.1)) := by
  simp only [weightedRow,List.map_map]
  apply List.map_congr_left
  intro term _
  simp only [Function.comp_apply,weightedClause,coefficient_decode t D ht hD model M cache]

theorem original_source_bytes {n : ℕ} (source : List (List (SAT.Literal (Fin n)))) :
    Encoding.encodeList id (encodedClauses source)=ExecQuantitativeSparsify.encodeRawFormula source := by
  rw [encodedClauses,ExecSparsifyEncoding.encodeList_map]
  rw [ExecQuantitativeSparsify.encodeRawFormula,ExecSparsifyEncoding.encodeList_map]
  congr 1
  funext ls
  exact clausePayload_codes ls

/-- The forward physical parser output is reversed by the paid command. Its
full shape dimension and exact original formula bytes suffice to produce the
interpreter's forward weighted-row input; no serialization premise is added. -/
theorem forward_original_eval {n : ℕ} (t D : ℕ) (ht : 0 < t) (hD : 0 < D)
    (b : ℕ) (hb : 0 < b) (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (encodedClauses source).length × ZMod 3))
    (hbound : 3*(encodedClauses source).length ≤ 2^b) (a : LeafProgram.Expansion.Data)
    (hraw : a.stacks 154=(Loop.rawInput b terms).reverse)
    (hsource : a.stacks 700=ExecQuantitativeSparsify.encodeRawFormula source)
    (hwidth : (a.stacks 708).length=b)
    (hmodulus : BinaryArithmetic.toNat (a.stacks 707)=(encodedClauses source).length)
    (hshape : (a.stacks 280).length=D*SubexpLiftRing.baseWidth 3 t)
    (houtput : a.stacks 64=[])
    (hwork : ∀ i∈LeafProgram.Expansion.scratch,a.stacks i=[])
    (h358 : a.stacks 358=[]) (h359 : a.stacks 359=[]) :
    ∃ k rf, k ≤ 9*(a.stacks 154).length+7+
        Loop.uniformBudget t (D-1) b (a.stacks 707) (encodedClauses source) terms.length+3 ∧
      Eval LeafProgram.Expansion.forwardCommand k a
        (LeafProgram.Expansion.finished (LeafProgram.Expansion.reversedInput a) rf
          (Encoding.encodeList id ((weightedRow t D source terms).map Row.payload))) := by
  have hdim : D-1+1=D := by omega
  have hs : a.stacks 700=Encoding.encodeList id (encodedClauses source) :=
    hsource.trans (original_source_bytes source).symm
  obtain ⟨k,rf,hk,he⟩ := LeafProgram.Expansion.forward_command_eval t (D-1) ht b hb
    (encodedClauses source) terms hbound a hraw hs hwidth hmodulus
    (by simpa only [hdim] using hshape) houtput hwork h358 h359
  rw [outputWord_eq t D hD source terms] at he
  exact ⟨k,rf,hk,he⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.Expansion

end OAI.Algorithms
