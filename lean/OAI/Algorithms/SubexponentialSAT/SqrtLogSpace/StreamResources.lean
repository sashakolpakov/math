import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Deterministic successful traces to halted states have the same length. -/
theorem halted_trace_steps_eq {α : Type*} {step : α → Option α}
    {n m : ℕ} {a b c : α} (hb : Computation.Trace step n a b)
    (hc : Computation.Trace step m a c) (hstopb : step b = none)
    (hstopc : step c = none) : n = m := by
  induction hb generalizing m c with
  | refl a =>
      cases hc with
      | refl => rfl
      | cons hs _ => simp [hstopb] at hs
  | @cons n a next b hs ht ih =>
      cases hc with
      | refl => simp [hstopc] at hs
      | @cons m _ next' _ hs' ht' =>
          have heq : next = next' := Option.some.inj (hs.symm.trans hs')
          subst next'
          exact congrArg Nat.succ (ih ht' hstopb hstopc)

/-- Structured evaluation has its actual measured length, independent of the
derivation used to establish its concrete execution. -/
theorem eval_steps_eq {r s : ℕ} {command : StructuredCalls.Cmd r s}
    (inputStack outputStack : Fin s) {n m : ℕ} {a b c : StructuredCalls.State r s}
    (hb : StructuredCalls.Eval command n a b)
    (hc : StructuredCalls.Eval command m a c) : n = m := by
  have h := halted_trace_steps_eq
    (StructuredCalls.compiled_halt_trace hb inputStack outputStack)
    (StructuredCalls.compiled_halt_trace hc inputStack outputStack)
    (by rfl) (by rfl)
  exact Nat.add_right_cancel h

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

/-- Every unassigned stack retains its caller contents at every actual prefix,
including prefixes within a relocated subroutine. -/
theorem relocate_trace_stack_frame {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps prefixSteps : ℕ} {a b : Cfg r s l} (tr : Trace p steps a b)
    {intermediate : Cfg R S L} (hle : prefixSteps ≤ steps)
    (hp : Trace q prefixSteps
      (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate)
    (i : Fin S) (hi : ¬ ∃ j, stack j = i) :
    intermediate.stacks i = frame.stacks i := by
  obtain ⟨source, _, rfl⟩ := StructuredSpace.relocate_trace_prefix p q register stack label
    returnPc frame hregister hstack hcode tr hle hp
  exact ProgramLinking.embedCfg_stack_frame register stack label returnPc frame source i hi

/-- Only unassigned caller ports need a frame bound, since assigned ports are
overwritten by the embedded source state. The instruction table and actual
source trace remain explicit. -/
theorem relocate_trace_stack_bound {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (¬ ∃ j, stack j = i) → (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace q prefixSteps
        (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hp i
  obtain ⟨source, hs, rfl⟩ := StructuredSpace.relocate_trace_prefix p q register stack label
    returnPc frame hregister hstack hcode tr hle hp
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [ProgramLinking.embedCfg_stack register stack label returnPc frame source hstack]
    exact (hsource prefixSteps source hle hs j).trans (Nat.le_max_left _ _)
  · rw [ProgramLinking.embedCfg_stack_frame register stack label returnPc frame source i hi]
    exact (hframe i hi).trans (Nat.le_max_right _ _)

/-- A locally bounded body may be repeated arbitrarily often. Its entry bound
includes every persistent caller stack, and its concrete runtime controls only
the temporary growth within that invocation. -/
theorem loop_local_stack_bound {r s : ℕ} (body : StructuredCalls.Cmd r s)
    (test : Fin r) (inputStack outputStack : Fin s)
    (I : StructuredCalls.State r s → Prop) (initialBound bodyTime : ℕ)
    (hinitial : ∀ a, I a → stackBits a.stacks ≤ initialBound)
    (hpreserve : ∀ n a b, StructuredCalls.Eval body n a b → I a →
      a.regs test = true → I b)
    (htime : ∀ n a b, StructuredCalls.Eval body n a b → I a →
      a.regs test = true → n ≤ bodyTime)
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval (.while test body) steps a b) (ha : I a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled (.while test body) inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled (.while test body) inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ initialBound + bodyTime := by
  apply StructuredSpace.loop_stack_bound body test inputStack outputStack I
    (initialBound + bodyTime) _ hpreserve _ heval ha
  · intro start hstart i
    have hi : (start.stacks i).length ≤ stackBits start.stacks :=
      Finset.single_le_sum (fun j _ => Nat.zero_le ((start.stacks j).length))
        (Finset.mem_univ i)
    exact hi.trans ((hinitial start hstart).trans (Nat.le_add_right _ _))
  · intro n start finish hbody hstart htest prefixSteps intermediate hle htrace i
    have hbound : dataBits
        (start.withPC (some (StructuredCalls.compiled body inputStack outputStack).entry)) ≤
        initialBound := hinitial start hstart
    exact StructuredSpace.local_stack_bound
      (StructuredCalls.compiled body inputStack outputStack) (steps := bodyTime)
      hbound prefixSteps intermediate (hle.trans (htime n start finish hbody hstart htest))
      htrace i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
