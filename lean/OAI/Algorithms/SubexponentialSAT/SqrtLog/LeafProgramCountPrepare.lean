import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramReady
import OAI.Algorithms.SubexponentialSAT.BankRoutines

namespace OAI.Algorithms

/-! Actual reclamation of node-work scratch before Hermite reconstruction.
The static port set includes both the native CRT work ports and the scalar/
polynomial arithmetic readiness ports, together with the reader temporaries. Runtime data are cleared by real
stack loops; persistent node and jet inputs remain outside this set. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

open SubexponentialSAT BitProgram StructuredCalls

def ports : List (Fin 768) :=
  (((ReconstructionProgram.NativeState.cleanPorts ++ ReconstructionProgram.InputReady.emptyPorts).map crtStacks) ++
    [323,324,325,326,327,328,329]).dedup

abbrev command : Cmd 40 768 :=
  .seq (.call (StackRoutines.clearProgram 699 0 1))
    (BankRoutines.clearCmd 699 0 1 ports)

def output (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    BankRoutines.clearBankStacks ports (Function.update a.stacks 699 [])⟩

def budget (a : Data) : ℕ :=
  2*(a.stacks 699).length+6+3*ports.length+
    2*(ports.map (fun i => (a.stacks i).length)).sum

private theorem ports_lt_aux (i : Fin 768) (hi : i ∈ ports) : i.val < 330 := by
  simp only [ports,List.mem_dedup,List.mem_append] at hi
  rcases hi with hi | hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    change j.val < 330
    omega
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with h|h|h|h|h|h|h <;> subst i <;> norm_num

theorem scratch_outside : (699 : Fin 768) ∉ ports := by
  intro h
  have := ports_lt_aux 699 h
  norm_num at this

theorem ports_nodup : ports.Nodup := List.nodup_dedup _

theorem command_eval (a : Data) : Eval command (budget a) a (output a) := by
  let mid : Data := ⟨readRegs a.regs 0 1 none,Function.update a.stacks 699 []⟩
  have h1 : Eval (.call (StackRoutines.clearProgram 699 0 1)) (2*(a.stacks 699).length+3) a mid :=
    Eval.call _ (ListRegisterProgram.clear_run (699 : Fin 768) (0 : Fin 40) 1 a.regs a.stacks)
  have h2 := BankRoutines.clear_eval (699 : Fin 768) (0 : Fin 40) 1 ports
    ports_nodup mid.regs mid.stacks (by simp [mid])
  have hm : ports.map (fun i => (mid.stacks i).length) = ports.map (fun i => (a.stacks i).length) := by
    apply List.map_congr_left
    intro i hi
    have hn : i ≠ 699 := by intro h; subst i; exact scratch_outside hi
    simp [mid,hn]
  rw [hm] at h2
  have hfinal : (⟨readRegs mid.regs 0 1 none,
      BankRoutines.clearBankStacks ports mid.stacks⟩ : Data) = output a := by
    simp only [output,mid,StackRoutines.readRegs_reset]
  rw [hfinal] at h2
  have he := h1.seq h2
  have hcost : (2*(a.stacks 699).length+3) +
      (2*(ports.map (fun i => (a.stacks i).length)).sum+3*ports.length+3) = budget a := by
    unfold budget
    omega
  rw [hcost] at he
  exact he

theorem output_clean (a : Data) (i : Fin 320)
    (hi : i ∈ ReconstructionProgram.NativeState.cleanPorts) :
    (output a).stacks (crtStacks i) = [] := by
  have hm : crtStacks i ∈ ports := by
    apply List.mem_dedup.mpr
    exact List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨i,List.mem_append.mpr (Or.inl hi),rfl⟩))
  simpa only [output] using
    (BankRoutines.clearBankStacks_mem (crtStacks i) ports
      (Function.update a.stacks 699 []) hm)

theorem output_arithmetic_clean (a : Data) (i : Fin 320)
    (hi : i ∈ ReconstructionProgram.InputReady.emptyPorts) :
    (output a).stacks (crtStacks i) = [] := by
  have hm : crtStacks i ∈ ports := by
    apply List.mem_dedup.mpr
    exact List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨i,List.mem_append.mpr (Or.inr hi),rfl⟩))
  simpa only [output] using
    (BankRoutines.clearBankStacks_mem (crtStacks i) ports
      (Function.update a.stacks 699 []) hm)

theorem output_reader (a : Data) (i : Fin 768)
    (hi : i ∈ ([323,324,325,326,327,328,329] : List (Fin 768))) :
    (output a).stacks i = [] := by
  have hm : i ∈ ports := by
    apply List.mem_dedup.mpr
    exact List.mem_append.mpr (Or.inr hi)
  simpa only [output] using
    (BankRoutines.clearBankStacks_mem i ports (Function.update a.stacks 699 []) hm)

theorem output_port (a : Data) (i : Fin 768) (hi : i∈ports) :
    (output a).stacks i=[] := by
  simpa only [output] using
    (BankRoutines.clearBankStacks_mem i ports (Function.update a.stacks 699 []) hi)

theorem output_frame (a : Data) (i : Fin 768) (hi : i ∉ ports) (ht : i ≠ 699) :
    (output a).stacks i = a.stacks i := by
  simp [output,BankRoutines.clearBankStacks,hi,ht]

theorem ports_lt (i : Fin 768) (hi : i ∈ ports) : i.val < 330 := by
  exact ports_lt_aux i hi

theorem ports_not_mem_of_ge (i : Fin 768) (hi : 330 ≤ i.val) : i ∉ ports := by
  intro hp
  exact (Nat.not_lt_of_ge hi) (ports_lt i hp)

/-- Ports between the native CRT bank and the explicit reader bank are not
cleared by count preparation. -/
theorem ports_gap (i : Fin 768) (hlo : 320 ≤ i.val) (hhi : i.val < 323) :
    i ∉ ports := by
  intro hi
  simp only [ports, List.mem_dedup, List.mem_append] at hi
  rcases hi with hi | hi
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp hi
    have hv := congrArg Fin.val hj
    simp [crtStacks] at hv
    omega
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num at hhi

theorem port_332_not_mem : (332 : Fin 768) ∉ ports := by
  intro hi
  have hlt := ports_lt 332 hi
  norm_num at hlt

theorem output_high_frame (a : Data) (i : Fin 768) (hi : 330 ≤ i.val) (ht : i ≠ 699) :
    (output a).stacks i = a.stacks i := by
  apply output_frame a i _ ht
  intro hm
  have hh := ports_lt i hm
  omega

/-- The parked source/layout masters, including 730 through 743, survive. -/
theorem output_parked (a : Data) (i : Fin 768) (hi : 730 ≤ i.val) :
    (output a).stacks i = a.stacks i := by
  apply output_high_frame a i (by omega)
  intro h
  have hv : i.val = 699 := congrArg Fin.val h
  omega

/-- In particular the actual ring metadata and the newly produced node/jet
streams survive the cleanup that establishes the CRT scratch condition. -/
def protectedInputs : List (Fin 768) :=
  [194,201,202,203,204,207,209,211,212,243,256,265,280,281,300]

private theorem native_inputs_disjoint : List.Disjoint
    (ReconstructionProgram.NativeState.cleanPorts.map crtStacks) protectedInputs := by
  simp [List.Disjoint, protectedInputs, ReconstructionProgram.NativeState.cleanPorts,
    ReconstructionProgram.NativeState.workingClean,
    ReconstructionProgram.Middle.cleanPorts,
    ReconstructionProgram.CofactorOuter.cleanPorts,
    ReconstructionProgram.Scalar.cleanPorts,
    ReconstructionProgram.Horner.cleanPorts,
    SubexpCRTOuterProgram.initialCleanPorts, CRTLocalProgram.localWork,
    SubexponentialSAT.SubexpConvolutionControl.bufferPorts,
    SubexpCRTOuterProgram.localPorts, crtStacks]

private theorem arithmetic_inputs_disjoint : List.Disjoint
    (ReconstructionProgram.InputReady.emptyPorts.map crtStacks) protectedInputs := by
  simp [List.Disjoint, protectedInputs, ReconstructionProgram.InputReady.emptyPorts, crtStacks]

private theorem reader_inputs_disjoint : List.Disjoint
    ([323,324,325,326,327,328,329] : List (Fin 768)) protectedInputs := by
  simp [List.Disjoint, protectedInputs]

theorem inputs_disjoint : List.Disjoint ports protectedInputs := by
  apply List.disjoint_left.mpr
  intro i hi hp
  simp only [ports,List.mem_dedup,List.map_append,List.mem_append] at hi
  rcases hi with hleft | hr
  · rcases hleft with hn | ha
    · exact (List.disjoint_left.mp native_inputs_disjoint) hn hp
    · exact (List.disjoint_left.mp arithmetic_inputs_disjoint) ha hp
  · exact (List.disjoint_left.mp reader_inputs_disjoint) hr hp

theorem protected_not_mem (i : Fin 768) (hi : i ∈ protectedInputs) : i ∉ ports := by
  intro hp
  exact (List.disjoint_left.mp inputs_disjoint) hp hi

theorem output_input (a : Data) (i : Fin 768)
    (hi : i ∈ ([194,201,202,203,204,207,209,211,212,243,256,265,280] : List (Fin 768))) :
    (output a).stacks i = a.stacks i := by
  apply output_frame
  · intro h
    apply (List.disjoint_left.mp inputs_disjoint) h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [protectedInputs]
  · intro h; subst i; simp at hi

theorem output_register_frame (a : Data) (i : Fin 40) (hi : 2 ≤ i.val) :
    (output a).regs i = a.regs i := by
  apply StackRoutines.readRegs_frame
  · intro h; subst i; simp at hi
  · intro h; subst i; simp at hi

theorem output_entry_empty (a : Data) :
    (output a).stacks 5 = [] ∧ (output a).stacks 10 = [] ∧
      (output a).stacks 261 = [] := by
  exact ⟨output_clean a 5 (by decide), output_clean a 10 (by decide),
    output_clean a 261 (by decide)⟩

def program := compiled command 256 256

theorem program_run (a : Data) : RunsIn program (budget a+1)
    (a.withPC (some program.entry)) ((output a).withPC none) :=
  ⟨budget a+1,le_rfl,compiled_halt_trace (command_eval a) 256 256⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

end OAI.Algorithms
