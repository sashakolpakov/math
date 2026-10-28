import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStorage
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.SubexpSetupBoundSpec

namespace OAI.Algorithms

/-! Exact composition and memory charging for fixed outer-leaf stages. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexpSetupStorage

theorem routes_wordBound (ps : List Route) (a : Data) (B : ℕ) (hb : WordBound B a) :
    WordBound B (routesState ps a) := by
  induction ps generalizing a with
  | nil => exact hb
  | cons p ps ih =>
    apply ih
    intro i
    by_cases hi : i=p.2
    · subst i; simpa [routed] using hb p.1
    · simpa [routed,hi] using hb i

theorem cleanup_budget_le (a : Data) (B : ℕ) (hb : WordBound B a) :
    LeafProgram.Cleanup.Wide.budget (projectState id workerStack a)+1 ≤ 1536*B+2348 := by
  have hsum : ((List.finRange 768).map (fun i => (a.stacks (workerStack i)).length)).sum ≤
      (List.finRange 768).length*B := by
    induction List.finRange 768 with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      have hi := hb (workerStack i)
      omega
  simp only [List.length_finRange] at hsum
  change 2*((List.finRange 768).map (fun i => (a.stacks (workerStack i)).length)).sum+2347+1 ≤ _
  omega

noncomputable def stageReturned {r s : ℕ} (inputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) : Data :=
  embedState register stack (routesState inputs a) out

noncomputable def stageSaved {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) : Data :=
  routesState outputs (stageReturned inputs register stack a out)

noncomputable def stageResult {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) : Data :=
  workerCleared (stageSaved inputs outputs register stack a out)

noncomputable def stageBudget {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) (budget : ℕ) : ℕ :=
  routesCost inputs a + budget +
    routesCost outputs (stageReturned inputs register stack a out) +
    LeafProgram.Cleanup.Wide.budget
      (projectState id workerStack (stageSaved inputs outputs register stack a out)) + 1

theorem stage_eval {r s l : ℕ} (inputs outputs : List Route)
    (p : Program r s l) (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hwork : ∀ i, stack i ≠ 767)
    (hi : ∀ q ∈ inputs, routeValid q) (ho : ∀ q ∈ outputs, routeValid q)
    (a : Data) (ht : a.stacks 767 = []) (out : State r s) (budget : ℕ)
    (run : RunsIn p budget
      ((projectState register stack (routesState inputs a)).withPC (some p.entry))
      (out.withPC none)) :
    ∃ n ≤ stageBudget inputs outputs register stack a out budget,
      Eval (stage inputs p register stack outputs) n a
        (stageResult inputs outputs register stack a out) := by
  have he1 := routes_eval inputs hi a ht
  have ht1 : (routesState inputs a).stacks 767 = [] :=
    (routes_frame inputs a 767 (fun q hq => (hi q hq).2.2)).trans ht
  obtain ⟨n,hn,he⟩ := run
  have he2 := eval_call_from_state p register stack (routesState inputs a) hr hs he
  have ht2 : (stageReturned inputs register stack a out).stacks 767 = [] := by
    exact (embedState_stack_frame register stack (routesState inputs a) out 767
      (by rintro ⟨i,h⟩; exact hwork i h)).trans ht1
  have he3 := routes_eval outputs ho (stageReturned inputs register stack a out) ht2
  have ht3 : (stageSaved inputs outputs register stack a out).stacks 767 = [] :=
    (routes_frame outputs (stageReturned inputs register stack a out) 767
      (fun q hq => (ho q hq).2.2)).trans ht2
  have he4 := clearWorker_eval (stageSaved inputs outputs register stack a out) ht3
  refine ⟨_,?_,he1.seq (he2.seq (he3.seq he4))⟩
  dsimp only [stageBudget]
  omega

theorem stageResult_empty {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) (i : Fin 768) :
    (stageResult inputs outputs register stack a out).stacks (workerStack i) = [] :=
  clearWorker_stack _ i

theorem stageResult_frame {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) (i : Fin 896) (hi : 768 ≤ i.val)
    (hinput : ∀ q ∈ inputs, q.2 ≠ i) (houtput : ∀ q ∈ outputs, q.2 ≠ i)
    (hstack : ∀ j, stack j ≠ i) :
    (stageResult inputs outputs register stack a out).stacks i = a.stacks i := by
  rw [stageResult,clearWorker_frame _ i hi,stageSaved,routes_frame _ _ _ houtput,
    stageReturned,embedState_stack_frame register stack (routesState inputs a) out i
      (by rintro ⟨j,hj⟩; exact hstack j hj),routes_frame _ _ _ hinput]

/-- Uniform linear overhead, including dirty subprogram output cleanup.
The native subprogram's own trace budget is the only non-storage term. -/
theorem stage_bounded_eval {r s l : ℕ} (inputs outputs : List Route)
    (p : Program r s l) (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hwork : ∀ i, stack i ≠ 767)
    (hi : ∀ q ∈ inputs, routeValid q) (ho : ∀ q ∈ outputs, routeValid q)
    (hli : inputs.length ≤ 32) (hlo : outputs.length ≤ 32)
    (a : Data) (B : ℕ) (hb : WordBound B a) (ht : a.stacks 767 = [])
    (out : State r s) (budget : ℕ)
    (run : RunsIn p budget
      ((projectState register stack (routesState inputs a)).withPC (some p.entry))
      (out.withPC none)) :
    ∃ n ≤ 10000*(B+budget+1),
      Eval (stage inputs p register stack outputs) n a
        (stageResult inputs outputs register stack a out) := by
  have hw1 := routes_wordBound inputs a B hb
  obtain ⟨n,hn,he⟩ := run
  have hcall := eval_call_from_state p register stack (routesState inputs a) hr hs he
  have hw2 : WordBound (B+budget) (stageReturned inputs register stack a out) :=
    SubexpSetupBoundSpec.wordBound_mono (SubexpSetupBoundSpec.eval_wordBound hw1 hcall)
      (Nat.add_le_add_left hn B)
  have hw3 := routes_wordBound outputs (stageReturned inputs register stack a out) (B+budget) hw2
  have hic := routes_cost_bound inputs a B hb
  have hoc := routes_cost_bound outputs (stageReturned inputs register stack a out) (B+budget) hw2
  have hcleanup := cleanup_budget_le (stageSaved inputs outputs register stack a out) (B+budget) hw3
  obtain ⟨steps,hsteps,hrun⟩ := stage_eval inputs outputs p register stack hr hs hwork hi ho
    a ht out budget ⟨n,hn,he⟩
  refine ⟨steps,?_,hrun⟩
  have hi32 := Nat.mul_le_mul_right (9*B+8) hli
  have ho32 := Nat.mul_le_mul_right (9*(B+budget)+8) hlo
  dsimp only [stageBudget] at hsteps
  omega

/-- A long-running subprogram may dirty its workspace. This standard bit
trace estimate charges that dirt by its actual number of instructions. -/
theorem eval_stackBits {a b : Data} {c : Cmd 40 896} {n : ℕ}
    (h : Eval c n a b) : stackBits b.stacks ≤ stackBits a.stacks+n+1 := by
  have hs := trace_dataBits (compiled c 0 0) (compiled_halt_trace h 0 0)
  simpa only [dataBits,StructuredProgram.State.withPC,Nat.add_assoc] using hs

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
