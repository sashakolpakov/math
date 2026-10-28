import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativePolynomial

namespace OAI.Algorithms

/-! Output width is bounded by the actual paid query time, even when an older
branch contract advertises a loose width. A primitive instruction can push at
most one bit on a fixed stack. This keeps the outer envelope linear in the
expensive query bound. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafProgram

private theorem instruction_stack_length {r s l : ℕ} (instr : Instr r s l)
    (a : Cfg r s l) (i : Fin s) :
    ((execInstr instr a).stacks i).length ≤ (a.stacks i).length+1 := by
  cases instr <;> try simp [execInstr]
  · rename_i stack src next
    by_cases hi : i=stack
    · subst i; simp
    · simp [hi]
  · rename_i stack value present next
    by_cases hi : i=stack
    · subst i; simp [List.length_tail]; omega
    · simp [hi]

private theorem step_stack_length {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l}
    (h : step p a=some b) (i : Fin s) : (b.stacks i).length ≤ (a.stacks i).length+1 := by
  cases hp : a.pc with
  | none => simp [step,hp] at h
  | some label =>
      simp [step,hp] at h
      rw [←h]
      exact instruction_stack_length _ _ i

theorem trace_stack_length {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) (i : Fin s) : (b.stacks i).length ≤ (a.stacks i).length+n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hh := step_stack_length p hs i
      omega

theorem eval_stack_length {r s : ℕ} {c : Cmd r s} {a b : State r s} {n : ℕ}
    (h : Eval c n a b) (i : Fin s) : (b.stacks i).length ≤ (a.stacks i).length+n+1 := by
  have hh := trace_stack_length (compiled c i i) (compiled_halt_trace h i i) i
  simpa only [StructuredProgram.State.withPC,Nat.add_assoc] using hh

theorem query_width_from_cost (query : Cmd 40 768) (count cost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : Marked.Wide.QueryValueContract query count cost width ready valid) :
    Marked.Wide.QueryValueContract query count cost (fun bits => cost bits+1) ready valid := by
  intro bits tail base hv hb
  obtain ⟨n,middle,hn,hr,ha,hv,_,hs,he⟩ := hq bits tail base hv hb
  have hl := eval_stack_length he 323
  have hzero : base.stacks 323=[] := hb.2.1
  have hl' : (middle.stacks 323).length ≤ n+1 := by
    simpa [RecordPrograms.state,Marked.Wide.recordPorts,hzero] using hl
  exact ⟨n,middle,hn,hr,ha,hv,hl'.trans (Nat.add_le_add_right hn 1),hs,he⟩

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
