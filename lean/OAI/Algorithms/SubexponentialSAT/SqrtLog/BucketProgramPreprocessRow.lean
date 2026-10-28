import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramPreprocessStep

namespace OAI.Algorithms

/-! A measured signed row scan, followed by a physical frame-order repair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def prePeek : PreCode := .base (.atom (.peek 10 0 1))
def preBody : PreCode := .seq preStep prePeek
def preLoop : PreCode := .while 1 preBody
abbrev preScan : PreCode := .seq prePeek preLoop

def preReady (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord)
    (out : List Bool) : PreData :=
  preState (readRegs regs 0 1 (signedWords xs).head?) W xs out

def preScanCost (W : List Bool) (xs : List SignedWord) : ℕ :=
  (xs.map (fun a => preStepCost W a+2)).sum+1

def preOutputLength (W : List Bool) (xs : List SignedWord) : ℕ :=
  (xs.map (fun a => W.length+a.2.length+a.1.length+1)).sum

theorem prePeek_eval (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord)
    (out : List Bool) : Eval prePeek 1 (preState regs W xs out)
      (preReady regs W xs out) := Eval.base (StructuredProgram.Eval.atom _ _)

theorem preLoop_eval (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord)
    (acc : List Bool) :
    ∃ t ≤ preScanCost W xs, ∃ rf ys,
      Eval preLoop t (preReady regs W xs acc)
        (preState rf W [] (words ys.reverse++acc)) ∧
      List.Forall₂ (shiftedWord W) xs ys := by
  induction xs generalizing regs acc with
  | nil =>
      refine ⟨1,by simp [preScanCost],(preReady regs W [] acc).regs,[],?_,.nil⟩
      change Eval (.while 1 preBody) 1 (preReady regs W [] acc)
        (preState (preReady regs W [] acc).regs W [] acc)
      convert (Eval.while_false
        (show (preReady regs W [] acc).regs 1=false by
          simp [preReady,preState,signedWords,readRegs]) :
        Eval (.while 1 preBody) 1 (preReady regs W [] acc) (preReady regs W [] acc)) using 1
      simp [preReady, preState, signedWords ]
  | cons a xs ih =>
      rcases a with ⟨P,N⟩
      obtain ⟨ts,hts,rs,word,hes,hword⟩ := preStep_eval
        (preReady regs W ((P,N)::xs) acc).regs W P N xs acc
      obtain ⟨tt,htt,rf,ys,het,hys⟩ := ih rs (Encoding.frame word++acc)
      have hg : (preReady regs W ((P,N)::xs) acc).regs 1=true := by
        cases P <;> simp [preReady,preState,signedWords,Encoding.frame,readRegs]
      have he := Eval.while_true hg (hes.seq (prePeek_eval rs W xs _)) het
      refine ⟨(ts+1)+tt+1,?_,rf,word::ys,?_,.cons hword hys⟩
      · simp only [preScanCost,List.map_cons,List.sum_cons] at *
        omega
      · change Eval (.while 1 preBody) _ _ _
        change Eval (.while 1 preBody) _ _ _ at he
        simpa [List.reverse_cons,words_append,words,List.append_assoc] using he

theorem preScan_eval_of_loop (regs : Fin 8 → Bool) (W : List Bool)
    (xs : List SignedWord) (t : ℕ) (rf : Fin 8 → Bool) (ys : List (List Bool))
    (ht : t ≤ preScanCost W xs)
    (he : Eval preLoop t (preReady regs W xs [])
      (preState rf W [] (words ys.reverse)))
    (hy : List.Forall₂ (shiftedWord W) xs ys) :
    ∃ t ≤ preScanCost W xs + 1, ∃ rf ys,
      Eval preScan t (preState regs W xs [])
        (preState rf W [] (words ys.reverse)) ∧
      List.Forall₂ (shiftedWord W) xs ys :=
  ⟨1 + t, by omega, rf, ys, (prePeek_eval regs W xs []).seq he, hy⟩

theorem preScan_eval_map (regs : Fin 8 → Bool) (W : List Bool)
    (xs : List SignedWord)
    (h : ∃ t ≤ preScanCost W xs, ∃ rf ys,
      Eval preLoop t (preReady regs W xs [])
        (preState rf W [] (words ys.reverse ++ [])) ∧
      List.Forall₂ (shiftedWord W) xs ys) :
    ∃ t ≤ preScanCost W xs + 1, ∃ rf ys,
      Eval preScan t (preState regs W xs [])
        (preState rf W [] (words ys.reverse)) ∧
      List.Forall₂ (shiftedWord W) xs ys := by
  obtain ⟨t, ht, rf, ys, he, hy⟩ := h
  rw [List.append_nil] at he
  exact preScan_eval_of_loop regs W xs t rf ys ht he hy

theorem preLoop_eval_empty (regs : Fin 8 → Bool) (W : List Bool)
    (xs : List SignedWord) :
    ∃ t ≤ preScanCost W xs, ∃ rf ys,
      Eval preLoop t (preReady regs W xs [])
        (preState rf W [] (words ys.reverse ++ [])) ∧
      List.Forall₂ (shiftedWord W) xs ys :=
  preLoop_eval regs W xs []

theorem preScan_eval (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord) :
    ∃ t ≤ preScanCost W xs+1, ∃ rf ys,
      Eval preScan t (preState regs W xs [])
        (preState rf W [] (words ys.reverse)) ∧ List.Forall₂ (shiftedWord W) xs ys := by
  exact preScan_eval_map regs W xs (preLoop_eval_empty regs W xs)

theorem shiftedWords_length {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys) : xs.length=ys.length := by
  induction h with
  | nil => rfl
  | cons h hs ih => simpa using ih

theorem shiftedWords_totalLength {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys) :
    (ys.map List.length).sum ≤ preOutputLength W xs := by
  induction h with
  | nil => simp [preOutputLength]
  | cons h hs ih =>
      simp only [List.map_cons,List.sum_cons,preOutputLength] at *
      exact Nat.add_le_add h.2 ih

theorem preWords_length (ys : List (List Bool)) :
    (words ys).length=2*(ys.map List.length).sum+ys.length := by
  induction ys with
  | nil => simp [words]
  | cons y ys ih => simp [words,Encoding.length_frame,ih]; omega

theorem preReverseCost_eq (ys : List (List Bool)) :
    preReverseCost ys=17*(ys.map List.length).sum+17*ys.length+1 := by
  induction ys with
  | nil => simp [preReverseCost]
  | cons y ys ih => simp only [preReverseCost,List.map_cons,List.sum_cons,List.length_cons] at *; omega

def preReversePorts : Fin 4 → Fin 14 := ![11,8,12,13]
theorem preReversePorts_injective : Function.Injective preReversePorts := by decide

def preRepair : PreCode := .seq
  (.call (ProgramLinking.liftProgram preReverseProgram id preReversePorts))
  (move 13 11 12)

def preRowCommand : PreCode := .seq preScan preRepair
def preRowProgram := compiled preRowCommand 10 11

def preRowCost (W : List Bool) (xs : List SignedWord) : ℕ :=
  preScanCost W xs+29*preOutputLength W xs+23*xs.length+20

theorem preRepair_eval (regs : Fin 8 → Bool) (W : List Bool) (ys : List (List Bool)) :
    ∃ rf, Eval preRepair (preReverseCost ys.reverse+2+6*(words ys).length+6)
      (preState regs W [] (words ys.reverse)) (preState rf W [] (words ys)) := by
  let d := preState regs W [] (words ys.reverse)
  have hp : projectState id preReversePorts d=preReverseState regs ys.reverse [] := by
    apply congrArg (StructuredProgram.State.mk regs)
    funext i; fin_cases i <;> rfl
  obtain ⟨rr,hr⟩ := preReverseCommand_eval regs ys.reverse []
  rw [←hp] at hr
  have hc := eval_call_from_state preReverseProgram id preReversePorts d
    Function.injective_id preReversePorts_injective (compiled_halt_trace hr 0 3)
  let e : PreData := ⟨rr,Function.update (Function.update d.stacks 11 []) 13 (words ys)⟩
  have he : embedState id preReversePorts d
      (preReverseState rr [] (words ys.reverse.reverse++[]))=e := by
    apply embedState_eq_of_ports id preReversePorts d _ _ Function.injective_id preReversePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [preReversePorts,e,d,preState,signedWords,words]
    · intro i hi
      have h11 : i≠11 := fun h => hi ⟨0,h.symm⟩
      have h13 : i≠13 := fun h => hi ⟨3,h.symm⟩
      simp [e,h11,h13]
  rw [he] at hc
  obtain ⟨f,hf,hsf⟩ := move_eval (13 : Fin 14) 11 12
    (by decide) (by decide) (by decide) e (by simp [e]) (by simp [e,d,preState])
  have he13 : e.stacks 13=words ys := by simp [e]
  have hend : f=preState f.regs W [] (words ys) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i; fin_cases i <;> simp [e,d,preState,signedWords]
  have hh := hc.seq hf
  rw [hend,he13] at hh
  exact ⟨f.regs, by simpa [preRepair, d, Nat.add_assoc] using hh⟩

theorem preRowCommand_eval (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord) :
    ∃ t ≤ preRowCost W xs, ∃ rf ys,
      Eval preRowCommand t (preState regs W xs []) (preState rf W [] (words ys)) ∧
      List.Forall₂ (shiftedWord W) xs ys := by
  obtain ⟨t,ht,rm,ys,he,hy⟩ := preScan_eval regs W xs
  obtain ⟨rf,hf⟩ := preRepair_eval rm W ys
  have hl := shiftedWords_totalLength hy
  have hn := shiftedWords_length hy
  refine ⟨_,?_,rf,ys,he.seq hf,hy⟩
  rw [preReverseCost_eq,preWords_length]
  simp only [List.length_reverse,List.map_reverse,List.sum_reverse]
  dsimp [preRowCost]
  omega

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
