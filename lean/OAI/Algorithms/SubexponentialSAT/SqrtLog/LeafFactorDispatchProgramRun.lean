import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgramChoose

namespace OAI.Algorithms

/-! Fixed native dispatcher: reverse the incoming ID, classify it, and scan
only the selected source. No selected payload is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def baseStacks (rows clauses : List (List Bool)) (m f : ℕ) : Fin 16 → List Bool :=
  ![Encoding.encodeList id rows,Encoding.encodeList id clauses,(Encoding.encodeNat f).reverse,
    unary rows.length,Encoding.encodeNat m,[],[],[],[],[],[],[],[],[],[],[]]

def input (regs : Fin 8 → Bool) (rows clauses : List (List Bool))
    (hasMarked : Bool) (m f : ℕ) : Data :=
  ⟨Function.update regs 7 hasMarked,baseStacks rows clauses m f⟩

def outputStacks (rows clauses : List (List Bool)) (hasMarked : Bool) (m f : ℕ) : Fin 16 → List Bool :=
  Function.update (Function.update (baseStacks rows clauses m f) 2 []) 15
    (selectedPayload rows clauses hasMarked m f)

def prepare : Code := .call (StackRoutines.transferProgram 2 6 0 1)
def command : Code := .seq prepare dispatch
def program := compiled command 2 15

def budget (rows clauses : List (List Bool)) (m f : ℕ) :=
  3*f+7+dispatchBound rows clauses m f

theorem program_runsIn (regs : Fin 8 → Bool) (rows clauses : List (List Bool))
    (hasMarked : Bool) (m f : ℕ) (hvalid : hasMarked=true → m < clauses.length) :
    ∃ rf, rf 5=decide (f < rows.length) ∧ rf 6=(hasMarked && decide (f=rows.length)) ∧
      rf 7=hasMarked ∧
      RunsIn program (budget rows clauses m f)
        ((input regs rows clauses hasMarked m f).withPC (some program.entry))
        ((⟨rf,outputStacks rows clauses hasMarked m f⟩ : Data).withPC none) := by
  let d := input regs rows clauses hasMarked m f
  let a := afterTransfer d 2 6 0 1
  have hp : Eval prepare (3*f+6) d a := by
    dsimp [a]
    simpa [prepare,d,input,baseStacks,Nat.mul_add,Nat.add_assoc] using
      transfer_eval d 2 6 0 1 (by decide) (by decide)
  obtain ⟨n,e,hn,he,hs,h5,h6,h7⟩ := dispatch_eval a rows clauses hasMarked m f
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,input,readRegs]) hvalid
    (by intro j hj; fin_cases j <;> simp_all [a,d,afterTransfer,
      StackRoutines.transferStacks,input,baseStacks])
    (by simp [TestClean,a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
  have hout : e.stacks=outputStacks rows clauses hasMarked m f := by
    rw [hs]
    funext j
    fin_cases j <;> simp [finishedStacks,a,d,afterTransfer,StackRoutines.transferStacks,
      input,baseStacks,outputStacks]
  have heq : e=(⟨e.regs,outputStacks rows clauses hasMarked m f⟩ : Data) := by
    exact state_ext rfl hout
  refine ⟨e.regs,h5,h6,?_,3*f+6+n+1,?_,?_⟩
  · simpa [a,d,afterTransfer,input,readRegs] using h7
  · unfold budget; omega
  · have ht := compiled_halt_trace (hp.seq he) 2 15
    rw [heq] at ht
    exact ht

theorem budget_linear (rows clauses : List (List Bool)) (m f : ℕ) :
    budget rows clauses m f ≤ 200*(f+m+rows.length+
      (Encoding.encodeList id rows).length+(Encoding.encodeList id clauses).length+1) := by
  unfold budget dispatchBound branchBound
  omega

theorem program_primitive (regs : Fin 8 → Bool) (rows clauses : List (List Bool))
    (hasMarked : Bool) (m f : ℕ) (hvalid : hasMarked=true → m < clauses.length) :
    ∃ rf, rf 5=decide (f < rows.length) ∧ rf 6=(hasMarked && decide (f=rows.length)) ∧
      rf 7=hasMarked ∧
      Computation.RunsIn (primitive program).step (primitiveOverhead program*budget rows clauses m f)
        (primitiveCfg program ((input regs rows clauses hasMarked m f).withPC (some program.entry)))
        (primitiveCfg program ((⟨rf,outputStacks rows clauses hasMarked m f⟩ : Data).withPC none)) := by
  obtain ⟨rf,h5,h6,h7,hr⟩ := program_runsIn regs rows clauses hasMarked m f hvalid
  exact ⟨rf,h5,h6,h7,primitive_execution program hr⟩

theorem source_frame (rows clauses : List (List Bool)) (hasMarked : Bool) (m f : ℕ)
    (i : Fin 16) (h2 : i≠2) (h15 : i≠15) :
    outputStacks rows clauses hasMarked m f i=baseStacks rows clauses m f i := by
  simp [outputStacks,h2,h15]

/-- The source master is exactly the existing executable leaf serialization. -/
theorem baseStacks_leaf {n : ℕ} (rows : List (List Bool))
    (F : ExecQuantitativeSparsify.Formula n) (m f : ℕ) :
    baseStacks rows (F.map HashInputProgram.clausePayload) m f 1 =
      ExecQuantitativeSparsify.encodeRawFormula F := by
  exact encode_clausePayloads F

/-- A marked factor returns the original clause's literal-code payload. -/
theorem selectedPayload_leaf_marked {n : ℕ} (rows : List (List Bool))
    (F : ExecQuantitativeSparsify.Formula n) (m : ℕ) (hm : m < F.length) :
    selectedPayload rows (F.map HashInputProgram.clausePayload) true m rows.length =
      HashInputProgram.clausePayload F[m] := by
  simp only [selectedPayload,lt_self_iff_false,ite_false,decide_true,Bool.and_self,ite_true]
  rw [List.getD_eq_getElem _ _ (by simpa using hm),List.getElem_map]

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
