import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramFrames
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Paid conversion of tagged record lists to the raw framed support stream. -/
namespace SubexponentialSAT.SqrtLog.LeafSupportInputProgram.Convert
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram
open SubexponentialSAT.SqrtLog.MomentsAssembly (rawFrames)

abbrev Data := State 3 3
abbrev Code := Cmd 3 3

abbrev state (regs : Fin 3 → Bool) (source payload output : List Bool) : Data :=
  ⟨regs,![source,payload,output]⟩
abbrev ports : RecordPrograms.Ports 3 3 := ⟨0,1,2,0,1,by decide,by decide,by decide,by decide⟩
abbrev escapePorts : RecordPrograms.Ports 3 3 := ⟨0,1,2,1,2,by decide,by decide,by decide,by decide⟩
abbrev callback : Code := .seq (pushConst 2 0 false)
  (.seq (escape escapePorts) (.base (.atom (.set 1 true))))
def command : Code := RecordPrograms.iterate ports callback
def program := compiled command 0 2

def effect (bits : List Bool) (a b : Data) : Prop :=
  b.stacks 2 = Encoding.frame bits ++ a.stacks 2

theorem callback_contract : RecordPrograms.CallbackContractWith ports callback
    (fun _ => false) (fun bits => 5*bits.length+6) (fun _ => True) effect := by
  intro bits tail base _
  let a := RecordPrograms.state ports base false true false tail bits.reverse
  let b := pushedState (2 : Fin 3) (0 : Fin 3) false a
  let c := escapedState escapePorts b
  let next : Data := ⟨base.regs,Function.update base.stacks 2 (Encoding.frame bits++base.stacks 2)⟩
  have h1 := pushConst_eval (2 : Fin 3) (0 : Fin 3) false a
  have h2 := escape_eval_state escapePorts b
  have h3 : Eval (.base (.atom (.set (1 : Fin 3) true))) 1 c
      ⟨Function.update c.regs 1 true,c.stacks⟩ := .base (.atom _ _)
  refine ⟨5*bits.length+6,next,le_rfl,trivial,?_,?_⟩
  · simp [effect,next]
  · convert h1.seq (h2.seq h3) using 1
    · simp [b,a,RecordPrograms.state]
      omega
    · apply congrArg₂ StructuredProgram.State.mk
      · funext i; fin_cases i <;>
          simp [next,c,b,a,RecordPrograms.state,ports,readRegs]
      · funext i; fin_cases i <;>
          simp [next,c,b,a,RecordPrograms.state,
            frame_eq_escaped,List.append_assoc]

theorem rawFrames_append (xs ys : List (List Bool)) :
    rawFrames (xs++ys)=rawFrames xs++rawFrames ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rawFrames,ih,List.append_assoc]

theorem fold_frames (xs : List (List Bool)) (acc : List Bool) :
    xs.foldl (fun out bits => Encoding.frame bits++out) acc = rawFrames xs.reverse++acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp [List.foldl_cons,ih,List.reverse_cons,rawFrames_append,rawFrames,List.append_assoc]

def cost (rows : List (List Bool)) : ℕ :=
  4+RecordPrograms.budget (fun bits => 5*bits.length+6) rows

theorem unread_false (rows : List (List Bool)) :
    RecordPrograms.unread (fun _ => false) rows []=[] := by
  induction rows with
  | nil => rfl
  | cons x xs ih => simpa [RecordPrograms.unread] using ih

theorem program_runsIn (regs : Fin 3 → Bool) (rows : List (List Bool)) :
    RunsIn program (cost rows)
      ((state regs (ProgramEncoding.encodeRecords rows) [] []).withPC (some program.entry))
      ((state ![false,true,false] [] [] (rawFrames rows.reverse)).withPC none) := by
  let a := state regs (ProgramEncoding.encodeRecords rows) [] []
  obtain ⟨t,b,ht,_,hv,he⟩ := RecordPrograms.iterate_run_with ports callback
    (fun _ => false) (fun bits => 5*bits.length+6) (fun _ => True) effect callback_contract
    rows [] a trivial (regs 0) (regs 1) (regs 2)
  have hstart : RecordPrograms.state ports a (regs 0) (regs 1) (regs 2)
      (Encoding.encodeList id rows++[]) [] = a := by
    apply RecordPrograms.state_eq_self <;> simp [a,ProgramEncoding.encodeRecords]
  have hout := hv.fold_of_false (by simp) (fun d => d.stacks 2)
    (fun out bits => Encoding.frame bits++out) (by intro bits a b h; exact h)
  have hout' : b.stacks 2=rawFrames rows.reverse := by
    calc
      b.stacks 2 = rows.foldl (fun out bits => Encoding.frame bits++out) (a.stacks 2) := hout
      _ = rawFrames rows.reverse++a.stacks 2 := fold_frames rows (a.stacks 2)
      _ = rawFrames rows.reverse := by simp [a]
  have hfinish : RecordPrograms.state ports b false true (rows.any (fun _ => false))
      (RecordPrograms.unread (fun _ => false) rows []) [] =
      state ![false,true,false] [] [] (rawFrames rows.reverse) := by
    rw [unread_false]
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [ports]
    · funext i; fin_cases i <;> simp [ports,hout']
  rw [hstart,hfinish] at he
  exact ⟨t+1,by dsimp [cost]; omega,compiled_halt_trace he 0 2⟩

theorem cost_uniform (rows : List (List Bool)) (n : ℕ)
    (h : ∀ row∈rows,row.length=n) : cost rows=4+rows.length*(11*n+13) := by
  unfold cost
  congr 1
  induction rows with
  | nil => simp [RecordPrograms.budget]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [RecordPrograms.budget,List.length_cons,hx,ht]
      ring

end SubexponentialSAT.SqrtLog.LeafSupportInputProgram.Convert

end OAI.Algorithms
