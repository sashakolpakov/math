import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputEntry

namespace OAI.Algorithms

/-! Exact five-port handoff from the native incidence producer to its loader. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Endpoint
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev Data := Install.Data

def outputStacks (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) : Fin 48 → List Bool :=
  fun j => if j=32 then Scan.scopeBits scopes else if j=33 then Scan.unary n
    else if j=34 then Scan.unary mask.length
    else if j=35 then Scan.unary (Semantics.factorCount scopes mask)
    else if j=45 then PairScoreProgram.pairRecords
      (PackingIncidenceProgram.generatedRawPairs (Install.plans scopes n mask)) else []

def result (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) : Data :=
  ⟨r,outputStacks scopes n mask⟩

def builtStacks (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) : Fin 48 → List Bool :=
  fun j => if j=32 then Scan.scopeBits scopes else if j=33 then Scan.unary n
    else if j=34 then Scan.unary mask.length
    else if j=35 then Scan.unary (Semantics.factorCount scopes mask)
    else if j=20 then ProgramEncoding.encodeRecords
      (PackingIncidenceProgram.planAlphabet (Install.plans scopes n mask)) else []

theorem produced_stacks (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (Install.produced r scopes n mask).stacks = builtStacks scopes n mask := by
  let d := Scan.data r scopes n mask.length (Semantics.factorCount scopes mask) []
    (ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet (Install.plans scopes n mask)))
  funext j
  by_cases hj : ∃ i, Install.ports i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [show (Install.produced r scopes n mask).stacks (Install.ports i) = d.stacks i from
      Install.state_stack d i]
    fin_cases i <;> simp [d,Scan.data,Install.ports,builtStacks]
  · rw [show (Install.produced r scopes n mask).stacks j = [] from
      Install.state_frame d j hj]
    have h32 : j ≠ 32 := fun h => hj ⟨20,h.symm⟩
    have h33 : j ≠ 33 := fun h => hj ⟨21,h.symm⟩
    have h34 : j ≠ 34 := fun h => hj ⟨22,h.symm⟩
    have h35 : j ≠ 35 := fun h => hj ⟨24,h.symm⟩
    have h20 : j ≠ 20 := fun h => hj ⟨25,h.symm⟩
    simp [builtStacks,h32,h33,h34,h35,h20]

theorem exact_output (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (e : Data)
    (hout : e.stacks 45 = PairScoreProgram.pairRecords
      (PackingIncidenceProgram.generatedRawPairs (Install.plans scopes n mask)))
    (hz : ∀ j, j=0 ∨ j=7 ∨ j ∈ PackingIncidenceProgram.Install.bank → e.stacks j = [])
    (hf : ∀ j, j≠0 → j≠7 → j≠45 → j ∉ PackingIncidenceProgram.Install.bank →
      e.stacks j = (Install.withDepth (Install.produced r scopes n mask)).stacks j) :
    e = result e.regs scopes n mask := by
  apply congrArg (StructuredProgram.State.mk e.regs)
  funext j
  by_cases hc : j=0 ∨ j=7 ∨ j ∈ PackingIncidenceProgram.Install.bank
  · rw [hz j hc]
    have h32 : j ≠ 32 := by intro h; subst j; simp [PackingIncidenceProgram.Install.bank] at hc
    have h33 : j ≠ 33 := by intro h; subst j; simp [PackingIncidenceProgram.Install.bank] at hc
    have h34 : j ≠ 34 := by intro h; subst j; simp [PackingIncidenceProgram.Install.bank] at hc
    have h35 : j ≠ 35 := by intro h; subst j; simp [PackingIncidenceProgram.Install.bank] at hc
    have h45 : j ≠ 45 := by intro h; subst j; simp [PackingIncidenceProgram.Install.bank] at hc
    simp only [outputStacks, ite_eq_right h32, ite_eq_right h33, ite_eq_right h34, ite_eq_right h35, ite_eq_right h45]
  · have h0 : j ≠ 0 := fun h => hc (Or.inl h)
    have h7 : j ≠ 7 := fun h => hc (Or.inr (Or.inl h))
    have hb : j ∉ PackingIncidenceProgram.Install.bank := fun h => hc (Or.inr (Or.inr h))
    by_cases h45 : j=45
    · subst j; simpa [outputStacks] using hout
    · have h20 : j ≠ 20 := by intro h; subst j; exact hb (by decide)
      have h27 : j ≠ 27 := by intro h; subst j; exact hb (by decide)
      rw [hf j h0 h7 h45 hb]
      simp [Install.withDepth,TupleProgram.pushedState,produced_stacks,
        builtStacks,outputStacks,h20,h27,h45]

/-- The installer returns exactly the five runtime metadata/data ports. -/
theorem install_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ t rf, t+1 ≤ Install.budget scopes n mask ∧
      Eval Install.command t (Install.input r scopes n mask) (result rf scopes n mask) := by
  obtain ⟨tb,rb,htb,hbuild⟩ := Install.build_eval r scopes n mask
  obtain ⟨ti,hti,e,he,hout,hz,hf⟩ := PackingIncidenceProgram.Install.command_eval
    (Install.plans scopes n mask) (Install.withDepth (Install.produced rb scopes n mask))
    (Install.installed_input rb scopes n mask)
  have hend := exact_output rb scopes n mask e hout hz hf
  have hrun := hbuild.seq ((Install.depth_eval _).seq he)
  rw [hend] at hrun
  exact ⟨tb+(4+ti),e.regs,by dsimp [Install.budget]; omega,hrun⟩

theorem install_runsIn (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ rf, RunsIn Install.program (Install.budget scopes n mask)
      ((Install.input r scopes n mask).withPC (some Install.program.entry))
      ((result rf scopes n mask).withPC none) := by
  obtain ⟨t,rf,ht,he⟩ := install_eval r scopes n mask
  exact ⟨rf,t+1,ht,compiled_halt_trace he 32 45⟩

/-- The descending-mask entry point has the same exact final state. -/
theorem entry_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ t rf, t+1 ≤ Entry.budget scopes n mask ∧
      Eval Entry.command t (Entry.input r scopes n mask) (result rf scopes n mask) := by
  obtain ⟨rm,hm⟩ := Entry.prepare_eval r scopes n mask
  obtain ⟨t,rf,ht,he⟩ := install_eval rm scopes n mask
  exact ⟨12*mask.length+12+t,rf,by dsimp [Entry.budget]; omega,hm.seq he⟩

theorem entry_runsIn (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ rf, RunsIn Entry.program (Entry.budget scopes n mask)
      ((Entry.input r scopes n mask).withPC (some Entry.program.entry))
      ((result rf scopes n mask).withPC none) := by
  obtain ⟨t,rf,ht,he⟩ := entry_eval r scopes n mask
  exact ⟨rf,t+1,ht,compiled_halt_trace he 32 45⟩

theorem entry_primitive (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ rf, Computation.RunsIn (primitive Entry.program).step
      (primitiveOverhead Entry.program * Entry.budget scopes n mask)
      (primitiveCfg Entry.program ((Entry.input r scopes n mask).withPC (some Entry.program.entry)))
      (primitiveCfg Entry.program ((result rf scopes n mask).withPC none)) := by
  obtain ⟨rf,hr⟩ := entry_runsIn r scopes n mask
  exact ⟨rf,BitProgram.primitive_execution Entry.program hr⟩

theorem entry_primitive_polynomial (r : Fin 16 → Bool) (scopes : List (List ℕ))
    (n : ℕ) (mask : List Bool) (hm : mask.length ≤ n) :
    ∃ rf, Computation.RunsIn (primitive Entry.program).step
      (primitiveOverhead Entry.program * (60000000*(Cost.inputSize scopes n mask)^5))
      (primitiveCfg Entry.program ((Entry.input r scopes n mask).withPC (some Entry.program.entry)))
      (primitiveCfg Entry.program ((result rf scopes n mask).withPC none)) := by
  obtain ⟨rf,hr⟩ := entry_primitive r scopes n mask
  exact ⟨rf,hr.mono (Nat.mul_le_mul_left _ (Finished.whole_input_polynomial scopes n mask hm))⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Endpoint

end OAI.Algorithms
