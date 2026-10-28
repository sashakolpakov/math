import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! Physical double framing for one vertex-plan alphabet entry. -/
namespace SubexponentialSAT.SubexpPlanAlphabetEmit

open BitProgram StructuredCalls Subexp.TupleProgram

abbrev Data := State 3 3

def data (regs : Fin 3 → Bool) (input scratch output : List Bool) : Data :=
  ⟨regs,![input,scratch,output]⟩

def innerPorts : RecordPrograms.Ports 3 3 :=
  ⟨0,1,2,1,0,by decide,by decide,by decide,by decide⟩
def outerPorts : RecordPrograms.Ports 3 3 :=
  ⟨0,1,2,1,2,by decide,by decide,by decide,by decide⟩

abbrev transfer : Cmd 3 3 := .call (StackRoutines.transferProgram 0 1 0 1)
def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,StackRoutines.transferStacks 0 1 d.stacks⟩
theorem transfer_eval (d : Data) :
    Eval transfer (3*(d.stacks 0).length+3) d (transferred d) :=
  .call _ (ListRegisterProgram.transfer_run 0 1 0 1 (by decide) (by decide) d.regs d.stacks)

abbrev command : Cmd 3 3 := .seq transfer (.seq (pushConst 0 0 false)
  (.seq (escape innerPorts) (.seq transfer (.seq (pushConst 2 0 false)
    (.seq (escape outerPorts) (pushConst 2 0 true))))))

/-- Consume a plan word and prepend a record whose payload is its frame.
Consequently two such payloads concatenate to a pair of framed plans. -/
theorem command_eval (regs : Fin 3 → Bool) (bits out : List Bool) :
    ∃ rf, Eval command (24*bits.length+26) (data regs bits [] out)
      (data rf [] [] (true::Encoding.frame (Encoding.frame bits)++out)) ∧ rf 2 = regs 2 := by
  let a := data regs bits [] out
  let a1 := transferred a
  let a2 := pushedState 0 0 false a1
  let a3 := escapedState innerPorts a2
  let a4 := transferred a3
  let a5 := pushedState 2 0 false a4
  let a6 := escapedState outerPorts a5
  let a7 := pushedState 2 0 true a6
  have h1 := transfer_eval a
  have h2 := pushConst_eval 0 0 false a1
  have h3 := escape_eval_state innerPorts a2
  have h4 := transfer_eval a3
  have h5 := pushConst_eval 2 0 false a4
  have h6 := escape_eval_state outerPorts a5
  have h7 := pushConst_eval 2 0 true a6
  have hinner : a3.stacks 0 = Encoding.frame bits := by
    simp [a3,innerPorts,a2,a1,transferred,
      StackRoutines.transferStacks,a,data,frame_eq_escaped]
  have hempty : a3.stacks 1 = [] := by
    simp [a3,innerPorts]
  have he : a7 = data a7.regs [] [] (true::Encoding.frame (Encoding.frame bits)++out) := by
    apply congrArg (StructuredProgram.State.mk a7.regs)
    funext i
    fin_cases i <;>
      simp [a6,outerPorts,a5,a4,transferred,
        StackRoutines.transferStacks,a3,innerPorts,a2,a1,a,data,
        frame_eq_escaped,List.append_assoc]
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))
  change Eval command _ a a7 at h
  rw [he] at h
  simp only [innerPorts,outerPorts] at h
  have hcost : (3*(a.stacks 0).length+3) +
      (2+((5*(a2.stacks 1).length+3)+
        ((3*(a3.stacks 0).length+3)+(2+((5*(a5.stacks 1).length+3)+2))))) =
      24*bits.length+26 := by
    simp [a5,a4,transferred,StackRoutines.transferStacks,hinner,hempty,
      a2,a1,a,data,Encoding.length_frame]
    omega
  refine ⟨a7.regs,?_,?_⟩
  · rw [hcost] at h
    exact h
  · simp [a7,a6,outerPorts,a5,a4,transferred,
      a3,innerPorts,a2,a1,a,data,readRegs]

abbrev program : Program 3 3 (size command+1) := compiled command 0 2

theorem program_trace (regs : Fin 3 → Bool) (bits out : List Bool) :
    ∃ rf, Trace program (24*bits.length+27)
      ((data regs bits [] out).withPC (some program.entry))
      ((data rf [] [] (true::Encoding.frame (Encoding.frame bits)++out)).withPC none) := by
  obtain ⟨rf,h,_⟩ := command_eval regs bits out
  exact ⟨rf,by simpa [Nat.add_assoc] using compiled_halt_trace h 0 2⟩

end SubexponentialSAT.SubexpPlanAlphabetEmit

end OAI.Algorithms
