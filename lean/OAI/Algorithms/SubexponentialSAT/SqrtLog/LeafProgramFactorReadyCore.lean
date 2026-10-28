import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyPhysical
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorDispatchFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorID

namespace OAI.Algorithms

/-! Physical framing for the factor loop, actual payload lookup, and incidence
staging. These lemmas describe states; no execution is an input hypothesis. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorReady
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage MomentsProgram
open PerturbationAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

def changes : List (Fin 768) := [149,150,151,154,556]
def Agree (s t : Fin 768 → List Bool) : Prop := ∀ i,i ∉ changes → s i=t i

theorem agree_refl (s : Fin 768 → List Bool) : Agree s s := fun _ _ => rfl

theorem copyMany_agree (ps : List (Fin 768 × Fin 768))
    (hp : ∀ p ∈ ps,p.1 ∉ changes ∧ p.2 ∉ changes)
    (a b : State 16 768) (h : Agree a.stacks b.stacks) :
    Agree (copyManyState ps a).stacks (copyManyState ps b).stacks := by
  induction ps generalizing a b with
  | nil => exact h
  | cons p ps ih =>
    apply ih (fun q hq => hp q (by simp [hq]))
    intro i hi
    rw [copyState_stack,copyState_stack]
    by_cases he : i=p.2
    · subst i
      simp only [Function.update_same]
      rw [h p.1 (hp p (by simp)).1,h p.2 (hp p (by simp)).2]
    · simp only [Function.update_of_ne he]
      exact h i hi

theorem staged_agree (a b : State 16 768) (h : Agree a.stacks b.stacks) :
    Agree (Incidence.staged a).stacks (Incidence.staged b).stacks := by
  have hc := copyMany_agree Incidence.pairs (by
    intro p hp
    simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      decide) a b h
  intro i hi
  change Function.update _ 550 _ i=Function.update _ 550 _ i
  by_cases he : i=550
  · subst i
    simp only [Function.update_same]
    rw [hc 138 (by decide),hc 550 (by decide)]
  · simp only [Function.update_of_ne he]
    exact hc i hi

theorem staged_changed (a : State 16 768) (i : Fin 768) (hi : i ∈ changes) :
    (Incidence.staged a).stacks i=a.stacks i := by
  apply Incidence.staged_frame
  · simp only [changes,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
  · intro p hp
    simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [changes,List.mem_cons,List.mem_nil_iff,or_false] at hi
    all_goals rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide

def payloadState {n B d : ℕ} (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (seed : FactorLoop.Raw n B d) (tail : List Bool) (f : ℕ) (payload : List Bool) : Factor.Data :=
  ⟨regs,Function.update (FactorLoop.state base regs seed tail (Encoding.encodeNat f).reverse).stacks 154 payload⟩

def workerState {n B d : ℕ} (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (seed : FactorLoop.Raw n B d) (tail : List Bool) (f : ℕ) (payload : List Bool) : State 16 768 :=
  projectState Incidence.callerRegisters id (FactorID.output (payloadState base regs seed tail f payload) f)

theorem worker_agree {n B d : ℕ} (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (seed : FactorLoop.Raw n B d) (tail : List Bool) (f : ℕ) (payload : List Bool) :
    Agree (workerState base regs seed tail f payload).stacks base := by
  intro i hi
  simp only [changes,List.mem_cons,List.mem_nil_iff,or_false,not_or] at hi
  simp [workerState,payloadState,FactorID.output,projectState,FactorLoop.state,
    hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2]

theorem worker_factor {n B d : ℕ} (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (seed : FactorLoop.Raw n B d) (tail : List Bool) (f : ℕ) (payload : List Bool) :
    (workerState base regs seed tail f payload).stacks 556=List.replicate f true := by
  simp [workerState,FactorID.output,projectState]

theorem actual_stacks {n B d : ℕ} (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (seed : FactorLoop.Raw n B d) (tail : List Bool) (f : ℕ) (rd : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark : ℕ)
    (hrows : base 701=Encoding.encodeList id rows)
    (hclauses : base 700=Encoding.encodeList id clauses)
    (hcount : base 704=List.replicate rows.length true)
    (hmark : base 705=Encoding.encodeNat mark)
    (hwork : ∀ i ∈ FactorDispatch.scratch,base i=[]) :
    (FactorDispatch.finished (FactorLoop.state base regs seed tail (Encoding.encodeNat f).reverse)
      rd rows clauses marked mark f).stacks=
    (payloadState base regs seed tail f
      (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark f)).stacks := by
  apply FactorDispatch.finished_stacks
  · simpa [FactorLoop.state] using hrows
  · simpa [FactorLoop.state] using hclauses
  · simpa [FactorLoop.state] using hcount
  · simpa [FactorLoop.state] using hmark
  · intro i hi
    have hn : i≠(149 : Fin 768) ∧ i≠150 ∧ i≠151 := by
      simp only [FactorDispatch.scratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        norm_num
    simpa [FactorLoop.state,hn.1,hn.2.1,hn.2.2] using hwork i hi

end SubexponentialSAT.SqrtLog.LeafProgram.FactorReady

end OAI.Algorithms
