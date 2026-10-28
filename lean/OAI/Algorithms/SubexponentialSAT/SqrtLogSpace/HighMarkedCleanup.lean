import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCleanup
/-! Actual lower-workspace reclamation in the shared leaf ABI. Source masters,
collector, count and upper caller words are preserved by the paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
abbrev Data := State 40 896
abbrev Code := Cmd 40 896
def stackMap : Fin 768 → Fin 896 := Fin.castAdd 128
def project (a : Data) : LeafProgram.Query.Data := projectState id stackMap a
noncomputable def result (a : Data) (b : LeafProgram.Query.Data) : Data := embedState id stackMap a b

@[simp] theorem result_stack (a : Data) (b : LeafProgram.Query.Data) (i : Fin 768) :
    (result a b).stacks (stackMap i)=b.stacks i :=
  embedState_stack id stackMap a b (Fin.castAdd_injective _ _) i

@[simp] theorem result_register (a : Data) (b : LeafProgram.Query.Data) (i : Fin 40) :
    (result a b).regs i=b.regs i := embedState_register id stackMap a b Function.injective_id i

@[simp] theorem project_result (a : Data) (b : LeafProgram.Query.Data) :
    project (result a b)=b := by
  apply congrArg₂ StructuredProgram.State.mk
  · exact funext (result_register a b)
  · exact funext (result_stack a b)

theorem result_upper_frame (a : Data) (b : LeafProgram.Query.Data) (i : Fin 896)
    (hi : (768 : ℕ) ≤ i.val) : (result a b).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

def cleanupLocalProgram := compiled LeafProgram.Query.cleanup 699 323
def cleanupCommand : Code := .call (ProgramLinking.liftProgram cleanupLocalProgram id stackMap)
def cleanupProgram := compiled cleanupCommand 699 323
noncomputable def cleaned (a : Data) : Data := result a (LeafProgram.Query.cleaned (project a))

@[simp] theorem cleaned_lower (a : Data) (i : Fin 768) :
    (cleaned a).stacks (stackMap i)=
      if LeafProgram.Query.Protected i then a.stacks (stackMap i) else [] := by
  rw [cleaned,result_stack,LeafProgram.Query.cleaned_stacks]
  rfl

theorem cleaned_upper (a : Data) (i : Fin 896) (hi : (768 : ℕ) ≤ i.val) :
    (cleaned a).stacks i=a.stacks i := result_upper_frame _ _ _ hi

theorem cleaned_count (a : Data) : (cleaned a).stacks 323=a.stacks 323 := by
  change (result a (LeafProgram.Query.cleaned (project a))).stacks (stackMap 323)=_
  rw [result_stack,LeafProgram.Query.cleaned_frame (project a) 323 (by decide)]
  rfl

theorem cleaned_register_frame (a : Data) (i : Fin 40) (hi : 2 ≤ i.val) :
    (cleaned a).regs i=a.regs i := by
  change (result a (LeafProgram.Query.cleaned (project a))).regs i=a.regs i
  rw [result_register]
  exact LeafProgram.Query.cleaned_register_frame (project a) i hi

theorem cleaned_parser (a : Data) :
    (cleaned a).regs 16=a.regs 16 ∧ (cleaned a).regs 17=a.regs 17 ∧
      (cleaned a).regs 18=a.regs 18 :=
  ⟨cleaned_register_frame a 16 (by decide),cleaned_register_frame a 17 (by decide),
    cleaned_register_frame a 18 (by decide)⟩

private theorem cleanup_source_space (a : LeafProgram.Query.Data) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ t z, t≤LeafProgram.Query.cleanupCost a → Trace cleanupLocalProgram t
      (a.withPC (some cleanupLocalProgram.entry)) z → ∀ i, (z.stacks i).length≤bound := by
  let middle : LeafProgram.Query.Data := ⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks 699 a.stacks⟩
  have he1 := BankRoutines.clear_call_eval (699 : Fin 768) (0 : Fin 40) 1 a.regs a.stacks
  have he2 := BankRoutines.clear_eval (699 : Fin 768) (0 : Fin 40) 1
    LeafProgram.Query.cleanupPorts LeafProgram.Query.cleanupPorts_nodup
    middle.regs middle.stacks (by simp [middle])
  have hfirst := HighQuerySpace.clear_bound (699 : Fin 768) (0 : Fin 40) 1 a bound hb 699 323
  have hsecond := HighQuerySpace.clear_bank_bound (699 : Fin 768) (0 : Fin 40) 1
    LeafProgram.Query.cleanupPorts LeafProgram.Query.cleanupPorts_nodup middle (by simp [middle]) bound
    (HighQuerySpace.clear_state_bound 699 0 1 a bound hb) 699 323
  have hwhole := StructuredSpace.sequence_stack_bound he1 he2 699 323 hfirst hsecond
    _ _ _ (compiled_site LeafProgram.Query.cleanup 699 323)
  have hmap : LeafProgram.Query.cleanupPorts.map (fun i => (middle.stacks i).length)=
      LeafProgram.Query.cleanupPorts.map (fun i => (a.stacks i).length) := by
    apply List.map_congr_left
    intro i hi
    have hn := (LeafProgram.Query.mem_cleanupPorts i).mp hi
    simp [middle,StackRoutines.clearStacks,hn.2]
  intro t z ht hz
  apply hwhole t z _ hz
  rw [hmap]
  dsimp [LeafProgram.Query.cleanupCost] at ht
  omega

/-- Reclaim all nonprotected lower words by actual pops, preserving the exact
count323, source masters, collector320/322 and every upper caller word. -/
theorem cleanup_trace_space (a : Data) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    Trace cleanupProgram (LeafProgram.Query.cleanupCost (project a)+2)
      (a.withPC (some cleanupProgram.entry)) ((cleaned a).withPC none) ∧
      LeafProgram.Query.cleanupCost (project a)+2≤1538*bound+2312 ∧
      ∀ t z, t≤LeafProgram.Query.cleanupCost (project a)+2 →
        Trace cleanupProgram t (a.withPC (some cleanupProgram.entry)) z →
        ∀ i, (z.stacks i).length≤bound := by
  have hsmall : ∀ i, ((project a).stacks i).length≤bound := fun i => hb (stackMap i)
  have he := LeafProgram.Query.cleanup_eval (project a)
  have ht := compiled_halt_trace he 699 323
  have hlocal := StructuredSpace.compiled_halt_stack_bound he 699 323
    (cleanup_source_space (project a) bound hsmall)
  have hev := eval_call_from_state cleanupLocalProgram id stackMap a
    Function.injective_id (Fin.castAdd_injective _ _) ht
  have hcall := HighQuerySpace.lifted_call_bound cleanupLocalProgram id stackMap
    Function.injective_id (Fin.castAdd_injective _ _) a (project a)
    (LeafProgram.Query.cleaned (project a)) rfl _ bound ht hlocal hb 699 323
  have htime := LeafProgram.Query.cleanupCost_le (project a) bound hsmall
  have hlen : LeafProgram.Query.cleanupPorts.length ≤ 768 :=
    LeafProgram.Query.cleanupPorts_length_le
  have hmul := Nat.mul_le_mul_right (2*bound+3) hlen
  refine ⟨compiled_halt_trace hev 699 323,by omega,?_⟩
  exact StructuredSpace.compiled_halt_stack_bound hev 699 323 hcall

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
