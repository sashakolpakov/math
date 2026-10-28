import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramController
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramPreprocessMatrix

namespace OAI.Algorithms

/-! Signed selected coefficient rows are physically converted before invoking
 the complete bucket controller. No precomputed shifted matrix is assumed. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Controller
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev PreData := State 10 25
abbrev PreCode := Cmd 10 25

def wideState (regs : Fin 10 → Bool) (W rows js n depth signed output : List Bool) : PreData :=
  ⟨regs,![W,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],rows,js,n,[],[],output,[],depth,signed]⟩

def preprocessPorts : Fin 17 → Fin 25 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,24,16,14]
theorem preprocessPorts_injective : Function.Injective preprocessPorts := by decide
abbrev corePorts : Fin 24 → Fin 25 := Fin.castAdd 1

def preprocessCall : PreCode := .call (ProgramLinking.liftProgram preMatrixProgram regs8 preprocessPorts)
def coreCall : PreCode := .call (ProgramLinking.liftProgram program id corePorts)
def signedCommand : PreCode := .seq preprocessCall coreCall
def signedProgram := compiled signedCommand 24 21

def signedInitial (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List SignedWord))
    (js : List ℕ) (n h : ℕ) : PreData :=
  wideState regs W [] (HeadScatterProgram.indices js) (HeadScatterProgram.unary n)
    (List.replicate h false) (words (rows.map signedWords)) []

def shiftedInitial (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) : PreData :=
  wideState regs W (words (rows.map words)) (HeadScatterProgram.indices js)
    (HeadScatterProgram.unary n) (List.replicate h false) [] []

def signedFinal (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) : PreData :=
  wideState regs W (words (rows.map words)) (HeadScatterProgram.indices js)
    (HeadScatterProgram.unary n) [] [] (tableOutput (labelledRecords W rows js n h))

theorem preprocess_eval (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List SignedWord))
    (js : List ℕ) (n h : ℕ) :
    ∃ t ≤ preMatrixCost W rows+1, ∃ rf ys,
      Eval preprocessCall t (signedInitial regs W rows js n h) (shiftedInitial rf W ys js n h) ∧
      List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys := by
  let d := signedInitial regs W rows js n h
  have hd : projectState regs8 preprocessPorts d=preMatrixState (regs ∘ regs8) W rows [] := by
    apply congrArg (StructuredProgram.State.mk (regs ∘ regs8))
    funext i; fin_cases i <;> simp [preprocessPorts,d,signedInitial,wideState]
  obtain ⟨rs,ys,⟨t,ht,he⟩,hy⟩ := preMatrixProgram_runsIn (regs ∘ regs8) W rows
  rw [←hd] at he
  have hc := eval_call_from_state preMatrixProgram regs8 preprocessPorts d
    (Fin.castAdd_injective _ _) preprocessPorts_injective he
  let out := preMatrixState rs W [] (words (ys.map words))
  let e := embedState regs8 preprocessPorts d out
  have hs : e=shiftedInitial e.regs W ys js n h := by
    apply embedState_eq_of_ports regs8 preprocessPorts d _ out
      (Fin.castAdd_injective _ _) preprocessPorts_injective
    · intro i; exact embedState_register regs8 preprocessPorts d out (Fin.castAdd_injective _ _) i
    · intro i hi; exact embedState_register_frame regs8 preprocessPorts d out i hi
    · intro i; fin_cases i <;>
        simp [preprocessPorts,shiftedInitial,wideState,out,preMatrixState,words]
    · intro i hi; fin_cases i <;>
        simp_all [Fin.exists_fin_succ,preprocessPorts,shiftedInitial,wideState,d,signedInitial]
  change Eval preprocessCall t d e at hc
  rw [hs] at hc
  exact ⟨t,ht,e.regs,ys,hc,hy⟩

theorem core_eval (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (hrows : ∀ row∈rows,row.length=h)
    (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    ∃ t ≤ cost W rows js n h, ∃ rf,
      Eval coreCall t (shiftedInitial regs W rows js n h) (signedFinal rf W rows js n h) := by
  let d := shiftedInitial regs W rows js n h
  have hd : projectState id corePorts d=initialState regs W rows js n h := by
    apply congrArg (StructuredProgram.State.mk regs)
    funext i; fin_cases i <;> simp [corePorts,d,shiftedInitial,wideState]
  obtain ⟨rf,t,ht,he⟩ := program_runsIn regs W rows js n h hrows hlen hjs
  rw [←hd] at he
  have hc := eval_call_from_state program id corePorts d Function.injective_id
    (Fin.castAdd_injective _ _) he
  have hs : embedState id corePorts d (finalState rf W rows js n h)=signedFinal rf W rows js n h := by
    apply embedState_eq_of_ports id corePorts d _ _ Function.injective_id (Fin.castAdd_injective _ _)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [corePorts,finalState,signedFinal,wideState,state]
    · intro i hi; fin_cases i <;>
        simp_all [Fin.exists_fin_succ,corePorts,signedFinal,wideState,d,shiftedInitial]
  change Eval coreCall t d (embedState id corePorts d (finalState rf W rows js n h)) at hc
  rw [hs] at hc
  exact ⟨t,ht,rf,hc⟩

theorem shiftedMatrix_width {W : List Bool} {rows : List (List SignedWord)}
    {ys : List (List (List Bool))} {h : ℕ}
    (hy : List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys)
    (hr : ∀ row∈rows,row.length=h) : ∀ row∈ys,row.length=h := by
  induction hy with
  | nil => simp
  | @cons row y rows ys hrow htail ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (shiftedWords_length hrow).symm.trans (hr row (by simp))
      · exact ih (by intro row hrow; exact hr row (by simp [hrow])) z hz

/-- The budget explicitly charges preprocessing and the actual produced matrix.
The polynomial input-only bound can be applied to the returned length contract. -/
theorem signedProgram_runsIn (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List SignedWord))
    (js : List ℕ) (n h : ℕ) (hrows : ∀ row∈rows,row.length=h)
    (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    ∃ rf ys, List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys ∧
      RunsIn signedProgram (preMatrixCost W rows+cost W ys js n h+2)
        ((signedInitial regs W rows js n h).withPC (some signedProgram.entry))
        ((signedFinal rf W ys js n h).withPC none) := by
  obtain ⟨a,ha,ra,ys,hea,hy⟩ := preprocess_eval regs W rows js n h
  obtain ⟨b,hb,rb,heb⟩ := core_eval ra W ys js n h (shiftedMatrix_width hy hrows) hlen hjs
  exact ⟨rb,ys,hy,a+b+1,by omega,compiled_halt_trace (hea.seq heb) 24 21⟩

end SubexponentialSAT.SqrtLog.BucketProgram.Controller

end OAI.Algorithms
