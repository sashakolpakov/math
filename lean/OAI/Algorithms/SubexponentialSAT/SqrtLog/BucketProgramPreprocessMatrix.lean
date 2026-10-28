import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramPreprocessRow

namespace OAI.Algorithms

/-! A concrete row-major signed matrix preprocessor. All input and output
frames are scanned by fixed instructions; the original bound word is retained. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev PreMatrixData := State 8 17
abbrev PreMatrixCode := Cmd 8 17

def preMatrixState (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) (out : List Bool) : PreMatrixData :=
  ⟨regs,![W,[],[],[],[],[],[],[],[],[],[],[],[],[],words (rows.map signedWords),out,[]]⟩

def preRowPorts : Fin 14 → Fin 17 := Fin.castAdd 3
def preRowCall : PreMatrixCode := .call
  (ProgramLinking.liftProgram preRowProgram id preRowPorts)

def preMatrixStep : PreMatrixCode := .seq (readWord 14 10 12 (by decide))
  (.seq preRowCall (emitFrame 11 15 12 (by decide)))

def preMatrixStepCost (W : List Bool) (row : List SignedWord) : ℕ :=
  9*(signedWords row).length+preRowCost W row+
    16*preOutputLength W row+8*row.length+16

theorem preMatrixStep_eval (regs : Fin 8 → Bool) (W : List Bool)
    (row : List SignedWord) (rows : List (List SignedWord)) (acc : List Bool) :
    ∃ t ≤ preMatrixStepCost W row, ∃ rf ys,
      Eval preMatrixStep t (preMatrixState regs W (row::rows) acc)
        (preMatrixState rf W rows (Encoding.frame (words ys)++acc)) ∧
      List.Forall₂ (shiftedWord W) row ys := by
  let d := preMatrixState regs W (row::rows) acc
  obtain ⟨a,ha,hsa⟩ := readWord_eval (14 : Fin 17) 10 12
    (by decide) (by decide) (by decide) d (signedWords row)
    (words (rows.map signedWords)) rfl rfl rfl
  have hp : projectState id preRowPorts a=preState a.regs W row [] := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    funext i; fin_cases i <;> simp [preRowPorts,hsa,d,preMatrixState]
  obtain ⟨tr,htr,rr,ys,hr,hy⟩ := preRowCommand_eval a.regs W row
  rw [←hp] at hr
  have hc := eval_call_from_state preRowProgram id preRowPorts a
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace hr 10 11)
  let e : PreMatrixData := ⟨rr,Function.update (Function.update a.stacks 10 []) 11 (words ys)⟩
  have he : embedState id preRowPorts a (preState rr W [] (words ys))=e := by
    apply embedState_eq_of_ports id preRowPorts a _ _ Function.injective_id
      (Fin.castAdd_injective _ _)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [preRowPorts,preState,e,hsa,d,preMatrixState,signedWords]
    · intro i hi
      have h10 : i≠10 := fun h => hi ⟨10,h.symm⟩
      have h11 : i≠11 := fun h => hi ⟨11,h.symm⟩
      simp [e,h10,h11]
  rw [he] at hc
  obtain ⟨f,hf,hsf⟩ := emitFrame_eval (11 : Fin 17) 15 12
    (by decide) (by decide) (by decide) e (by simp [e,hsa,d,preMatrixState])
  have he11 : e.stacks 11=words ys := by simp [e]
  have hend : f=preMatrixState f.regs W rows (Encoding.frame (words ys)++acc) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i; fin_cases i <;> simp [e,hsa,d,preMatrixState]
  have hall := ha.seq (hc.seq hf)
  rw [hend] at hall
  have hl := shiftedWords_totalLength hy
  have hn := shiftedWords_length hy
  refine ⟨_,?_,f.regs,ys,hall,hy⟩
  rw [he11,preWords_length]
  dsimp [preMatrixStepCost]
  omega

def preMatrixPeek : PreMatrixCode := .base (.atom (.peek 14 0 1))
def preMatrixBody : PreMatrixCode := .seq preMatrixStep preMatrixPeek
def preMatrixLoop : PreMatrixCode := .while 1 preMatrixBody
def preMatrixScan : PreMatrixCode := .seq preMatrixPeek preMatrixLoop

def preMatrixReady (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) (acc : List Bool) : PreMatrixData :=
  preMatrixState (readRegs regs 0 1 (words (rows.map signedWords)).head?) W rows acc

def preMatrixScanCost (W : List Bool) (rows : List (List SignedWord)) : ℕ :=
  (rows.map (fun row => preMatrixStepCost W row+2)).sum+1

theorem preMatrixPeek_eval (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) (acc : List Bool) :
    Eval preMatrixPeek 1 (preMatrixState regs W rows acc) (preMatrixReady regs W rows acc) :=
  Eval.base (StructuredProgram.Eval.atom _ _)

theorem preMatrixLoop_eval (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) (acc : List Bool) :
    ∃ t ≤ preMatrixScanCost W rows, ∃ rf ys,
      Eval preMatrixLoop t (preMatrixReady regs W rows acc)
        (preMatrixState rf W [] (words (ys.map words).reverse++acc)) ∧
      List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys := by
  induction rows generalizing regs acc with
  | nil =>
      refine ⟨1,by simp [preMatrixScanCost],readRegs regs 0 1 none,[],?_,.nil⟩
      simpa [preMatrixLoop, preMatrixReady, words] using (Eval.while_false
        (show (preMatrixReady regs W [] acc).regs 1=false by
          simp [preMatrixReady,preMatrixState,words,readRegs]) :
        Eval preMatrixLoop 1 (preMatrixReady regs W [] acc) (preMatrixReady regs W [] acc))
  | cons row rows ih =>
      obtain ⟨ts,hts,rs,y,hes,hy⟩ := preMatrixStep_eval
        (preMatrixReady regs W (row::rows) acc).regs W row rows acc
      obtain ⟨tt,htt,rf,ys,het,hys⟩ := ih rs (Encoding.frame (words y)++acc)
      have hg : (preMatrixReady regs W (row::rows) acc).regs 1=true := by
        cases hr : signedWords row <;> simp [preMatrixReady,preMatrixState,words,Encoding.frame,readRegs,hr]
      have he := Eval.while_true hg (hes.seq (preMatrixPeek_eval rs W rows _)) het
      refine ⟨(ts+1)+tt+1,?_,rf,y::ys,?_,.cons hy hys⟩
      · simp only [preMatrixScanCost,List.map_cons,List.sum_cons] at *; omega
      · simpa [preMatrixLoop,preMatrixBody,List.reverse_cons,words_append,words,
          List.append_assoc] using he

def preMatrixPayload (W : List Bool) (rows : List (List SignedWord)) : ℕ :=
  (rows.map (fun row => 2*preOutputLength W row+row.length)).sum

theorem shiftedMatrix_lengths {W : List Bool} {rows : List (List SignedWord)}
    {ys : List (List (List Bool))} (h : List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys) :
    rows.length=ys.length ∧ ((ys.map words).map List.length).sum ≤ preMatrixPayload W rows := by
  induction h with
  | nil => simp [preMatrixPayload]
  | cons h hs ih =>
      have hl := shiftedWords_totalLength h
      have hn := shiftedWords_length h
      simp only [List.length_cons,List.map_cons,List.sum_cons,preWords_length,preMatrixPayload] at *
      constructor <;> omega

def preMatrixReversePorts : Fin 4 → Fin 17 := ![15,11,12,16]
theorem preMatrixReversePorts_injective : Function.Injective preMatrixReversePorts := by decide

def preMatrixRepair : PreMatrixCode := .seq
  (.call (ProgramLinking.liftProgram preReverseProgram id preMatrixReversePorts)) (move 16 15 12)
def preMatrixCommand : PreMatrixCode := .seq preMatrixScan preMatrixRepair
def preMatrixProgram := compiled preMatrixCommand 14 15

def preMatrixCost (W : List Bool) (rows : List (List SignedWord)) : ℕ :=
  preMatrixScanCost W rows+29*preMatrixPayload W rows+23*rows.length+20

theorem preMatrixRepair_eval (regs : Fin 8 → Bool) (W : List Bool) (ys : List (List Bool)) :
    ∃ rf, Eval preMatrixRepair (preReverseCost ys.reverse+2+6*(words ys).length+6)
      (preMatrixState regs W [] (words ys.reverse)) (preMatrixState rf W [] (words ys)) := by
  let d := preMatrixState regs W [] (words ys.reverse)
  have hp : projectState id preMatrixReversePorts d=preReverseState regs ys.reverse [] := by
    apply congrArg (StructuredProgram.State.mk regs)
    funext i; fin_cases i <;> rfl
  obtain ⟨rr,hr⟩ := preReverseCommand_eval regs ys.reverse []
  rw [←hp] at hr
  have hc := eval_call_from_state preReverseProgram id preMatrixReversePorts d
    Function.injective_id preMatrixReversePorts_injective (compiled_halt_trace hr 0 3)
  let e : PreMatrixData := ⟨rr,Function.update (Function.update d.stacks 15 []) 16 (words ys)⟩
  have he : embedState id preMatrixReversePorts d
      (preReverseState rr [] (words ys.reverse.reverse++[]))=e := by
    apply embedState_eq_of_ports id preMatrixReversePorts d _ _ Function.injective_id preMatrixReversePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [preMatrixReversePorts,e,d,preMatrixState,words]
    · intro i hi
      have h15 : i≠15 := fun h => hi ⟨0,h.symm⟩
      have h16 : i≠16 := fun h => hi ⟨3,h.symm⟩
      simp [e,h15,h16]
  rw [he] at hc
  obtain ⟨f,hf,hsf⟩ := move_eval (16 : Fin 17) 15 12
    (by decide) (by decide) (by decide) e (by simp [e]) (by simp [e,d,preMatrixState])
  have he16 : e.stacks 16=words ys := by simp [e]
  have hend : f=preMatrixState f.regs W [] (words ys) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i; fin_cases i <;> simp [e,d,preMatrixState,words]
  have hall := hc.seq hf
  rw [hend,he16] at hall
  refine ⟨f.regs, ?_⟩
  convert hall using 1
  · rfl

theorem preMatrixCommand_eval (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) :
    ∃ t ≤ preMatrixCost W rows, ∃ rf ys,
      Eval preMatrixCommand t (preMatrixState regs W rows [])
        (preMatrixState rf W [] (words (ys.map words))) ∧
      List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys := by
  obtain ⟨ts,hts,rs,ys,hs,hys⟩ := preMatrixLoop_eval regs W rows []
  have hscan := (preMatrixPeek_eval regs W rows []).seq hs
  obtain ⟨rf,hr⟩ := preMatrixRepair_eval rs W (ys.map words)
  simp only [List.append_nil] at hscan
  have hl := shiftedMatrix_lengths hys
  refine ⟨_,?_,rf,ys,hscan.seq hr,hys⟩
  rw [preReverseCost_eq,preWords_length]
  simp only [List.length_reverse,List.length_map,List.map_reverse,List.sum_reverse]
  dsimp [preMatrixCost]
  omega

theorem preMatrixProgram_runsIn (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) :
    ∃ rf ys, RunsIn preMatrixProgram (preMatrixCost W rows+1)
      ((preMatrixState regs W rows []).withPC (some preMatrixProgram.entry))
      ((preMatrixState rf W [] (words (ys.map words))).withPC none) ∧
      List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys := by
  obtain ⟨t,ht,rf,ys,he,hy⟩ := preMatrixCommand_eval regs W rows
  exact ⟨rf,ys,⟨t+1,by omega,compiled_halt_trace he 14 15⟩,hy⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
