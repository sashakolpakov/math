import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgramFrames

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

def registers : Fin 16 → Fin 40 := Fin.castAdd 24
def project (a : Data) : LocalData := ⟨a.regs ∘ registers,a.stacks⟩
abbrev lifted (cmd : Cmd 16 768) : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram (compiled cmd 128 5) registers id)
abbrev command : Cmd 40 768 := lifted localCommand
abbrev cleanup : Cmd 40 768 := lifted localCleanup
def budget (a : Data) := localBudget (project a)+1
def cleanupBudget (a : Data) := clearManyCost cachePorts (project a)+1

private theorem lifted_eval (cmd : Cmd 16 768) (a : Data) (b : LocalData) {t : ℕ}
    (he : Eval cmd t (project a) b) :
    Eval (lifted cmd) (t+1) a (embedState registers id a b) := by
  exact eval_call_from_state (compiled cmd 128 5) registers id a
    (Fin.castAdd_injective _ _) Function.injective_id (compiled_halt_trace he 128 5)

private theorem installed_stacks (a : Data) (b : LocalData) :
    (embedState registers id a b).stacks=b.stacks := by
  funext i
  exact embedState_stack registers id a b Function.injective_id i

private theorem installed_registers (a : Data) (b : LocalData) (i : Fin 40) (hi : 16 ≤ i.val) :
    (embedState registers id a b).regs i=a.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  have hlt := j.isLt
  simp only [registers,Fin.val_castAdd] at hv
  omega

/-- The fixed global staging program modifies only registers below 16 and
exactly the advertised cache tapes. Its private pocket is empty on return. -/
theorem command_eval (a : Data) (h : Ready a.stacks) :
    ∃ b, Eval command (budget a) a b ∧ b.stacks=cacheTapes (project a) ∧
      (∀ i : Fin 40, 16 ≤ i.val → b.regs i=a.regs i) := by
  obtain ⟨out,he,hs⟩ := local_eval_exact (project a) h
  refine ⟨embedState registers id a out,lifted_eval localCommand a out he,?_,?_⟩
  · exact (installed_stacks a out).trans hs
  · exact installed_registers a out

theorem budget_le (a : Data) (B : ℕ) (ha : WordBound B a) : budget a ≤ 1001*(B+1) := by
  have hh := localBudget_le (project a) B ha
  unfold budget
  omega

/-- Exit cleanup has an actual trace and retains every tape outside the cache
bank, including all masters, the source block and the private pocket. -/
theorem cleanup_eval (a : Data) :
    ∃ b, Eval cleanup (cleanupBudget a) a b ∧
      (∀ i, b.stacks i=if i∈cachePorts then [] else a.stacks i) ∧
      (∀ i : Fin 40, 16 ≤ i.val → b.regs i=a.regs i) := by
  let out := clearManyState cachePorts (project a)
  have he := local_cleanup (project a)
  refine ⟨embedState registers id a out,lifted_eval localCleanup a out he,?_,?_⟩
  · intro i
    rw [installed_stacks]
    exact clearMany_stacks cachePorts (project a) i
  · exact installed_registers a out

theorem cleanupBudget_le (a : Data) (B : ℕ) (ha : WordBound B a) :
    cleanupBudget a ≤ 50*(B+1) := by
  have hh := clearManyCost_le cachePorts (project a) B ha
  change clearManyCost cachePorts (project a)  ≤ 14*(2*B+3) at hh
  unfold cleanupBudget
  omega

theorem cleanup_restore (a b : Data) (ha : Ready a.stacks)
    (hb : b.stacks=cacheTapes (project a)) :
    ∃ c, Eval cleanup (cleanupBudget b) b c ∧ c.stacks=a.stacks ∧
      (∀ i : Fin 40, 16 ≤ i.val → c.regs i=b.regs i) := by
  obtain ⟨c,he,hs,hr⟩ := cleanup_eval b
  refine ⟨c,he,?_,hr⟩
  funext i
  rw [hs]
  by_cases hi : i∈cachePorts
  · rw [ite_eq_left hi]
    exact (ha i (List.mem_append_left _ hi)).symm
  · rw [ite_eq_right hi,hb,cache_frame (project a) i hi]
    rfl

def program := compiled command 128 5
def cleanupProgram := compiled cleanup 128 5

theorem program_runs (a : Data) (h : Ready a.stacks) :
    ∃ b : Data, b.stacks=cacheTapes (project a) ∧
      (∀ i : Fin 40, 16 ≤ i.val → b.regs i=a.regs i) ∧
      RunsIn program (budget a+1) (a.withPC (some program.entry)) (b.withPC none) := by
  obtain ⟨b,he,hs,hr⟩ := command_eval a h
  exact ⟨b,hs,hr,_,le_rfl,compiled_halt_trace he 128 5⟩

end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
