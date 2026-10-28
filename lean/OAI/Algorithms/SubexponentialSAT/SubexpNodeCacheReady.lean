import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheStage
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkspace

namespace OAI.Algorithms

/-!
# Cache readiness from the actual active-node workspace

The six preparation copies and the existing cache port relocation are used
directly. Every scratch assertion follows from `activeStacks`; no cache
invariant or execution trace is supplied as an input assumption.
-/

namespace SubexponentialSAT.SubexpNodeCacheReady

open BitProgram StructuredCalls SubexpHornerControl SubexpTaylorControl
open SubexpNodeCacheStage (Data localState)

/-- Restriction used when the 256-stack cache stage runs inside the wider
288-stack node workspace. It changes no byte order or port numbers. -/
def activeStore (masters : SubexpNodeWorkspace.Store) (node : List Bool) :
    Fin 256 → List Bool :=
  fun i => SubexpNodeWorkspace.activeStacks masters node (Fin.castAdd 32 i)

/-- Empty inputs required by the existing physical preparation and cache call. -/
def emptyPorts : List (Fin 256) := [0,100,101,66,73,74,81,102,103,104,108]

theorem initial_empty (masters : SubexpNodeWorkspace.Store) (node : List Bool)
    (d : Data) (hactive : d.stacks = activeStore masters node)
    (i : Fin 256) (hi : i ∈ emptyPorts) : d.stacks i = [] := by
  rw [hactive]
  simp only [emptyPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- The row workspace has precisely the five populated Horner cells.
In particular, the cache's local 5, 10 and 25 refer to empty relocated
cells 112--114, rather than the persistent modulus/width/slot masters. -/
theorem prepared_row_formula (masters : SubexpNodeWorkspace.Store) (node : List Bool)
    (d : Data) (hactive : d.stacks = activeStore masters node) (i : Fin 90) :
    (localState (SubexpNodeCacheSetup.prepared d)).stacks
        (SubexpTaylorCacheControl.rowStacks i) =
      if i = 66 then masters 5 else
      if i = 73 then masters 91 else
      if i = 74 then masters 10 else
      if i = 78 then node else
      if i = 81 then SubexpNodeCacheSetup.width4 (masters 10) else [] := by
  simp only [localState, Function.comp_apply, SubexpNodeCacheSetup.prepared,
    SubexpNodeCacheSetup.preparedStacks, hactive]
  fin_cases i <;> rfl

theorem prepared_empty (masters : SubexpNodeWorkspace.Store) (node : List Bool)
    (d : Data) (hactive : d.stacks = activeStore masters node)
    (i : Fin 112) (hi : i ∈ ([109,110,105,106,107] : List (Fin 112))) :
    (localState (SubexpNodeCacheSetup.prepared d)).stacks i = [] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [localState, Function.comp_apply, SubexpNodeCacheSetup.prepared,
      SubexpNodeCacheSetup.preparedStacks, hactive]
    rfl

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

omit [Fact (Nat.Prime p)] in
theorem rowState_formula (reduction theta : SubexpTaylorRow.Code p μ)
    (width : List Bool) (regs : Fin 8 → Bool) (i : Fin 90) :
    (SubexpTaylorRow.rowState regs
        (done (SubexpHornerMachine.baseWords p μ M reduction theta width
          (SubexpNodeCacheSetup.width4 width)) []) [] [] []).stacks i =
      if i = 66 then M.bits else
      if i = 73 then SubexpTaylorRow.flat reduction else
      if i = 74 then width else
      if i = 78 then SubexpTaylorRow.flat theta else
      if i = 81 then SubexpNodeCacheSetup.width4 width else [] := by
  fin_cases i <;> rfl

omit [Fact (Nat.Prime p)] in
/-- All premises concern the actual active workspace and physical masters.
The needed invariant is a conclusion, including the relocated scratch cells. -/
theorem prepared_invariant (reduction theta : SubexpTaylorRow.Code p μ)
    (width : List Bool) (N : ℕ) (masters : SubexpNodeWorkspace.Store)
    (node : List Bool) (d : Data) (hactive : d.stacks = activeStore masters node)
    (hnode : node = SubexpTaylorRow.flat theta)
    (h5 : masters 5 = M.bits) (h10 : masters 10 = width)
    (h91 : masters 91 = SubexpTaylorRow.flat reduction)
    (h126 : masters 126 = List.replicate N true) :
    SubexpTaylorCacheMap.incidenceInvariant
      (SubexpHornerMachine.baseWords p μ M reduction theta width
        (SubexpNodeCacheSetup.width4 width)) N
      (localState (SubexpNodeCacheSetup.prepared d)) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i
    rw [prepared_row_formula masters node d hactive i, rowState_formula]
    simp only [hnode, h5, h10, h91]
  · change d.stacks 126 = List.replicate N true
    rw [hactive]
    exact h126
  all_goals exact prepared_empty masters node d hactive _ (by decide)

omit [Fact (Nat.Prime p)] in
/-- The existing charged copy program establishes readiness from the same
physical facts. No trace hypothesis is needed for this join. -/
theorem prepare_eval_and_ready (reduction theta : SubexpTaylorRow.Code p μ)
    (width : List Bool) (N : ℕ) (masters : SubexpNodeWorkspace.Store)
    (node : List Bool) (d : Data) (hactive : d.stacks = activeStore masters node)
    (hnode : node = SubexpTaylorRow.flat theta)
    (h5 : masters 5 = M.bits) (h10 : masters 10 = width)
    (h91 : masters 91 = SubexpTaylorRow.flat reduction)
    (h126 : masters 126 = List.replicate N true) :
    Eval SubexpNodeCacheSetup.prepare (SubexpNodeCacheSetup.prepareCost d) d
      (SubexpNodeCacheSetup.prepared d) ∧
    SubexpTaylorCacheMap.incidenceInvariant
      (SubexpHornerMachine.baseWords p μ M reduction theta width
        (SubexpNodeCacheSetup.width4 width)) N
      (localState (SubexpNodeCacheSetup.prepared d)) := by
  refine ⟨?_, prepared_invariant p μ M reduction theta width N masters node d
    hactive hnode h5 h10 h91 h126⟩
  apply SubexpNodeCacheSetup.prepare_eval
  all_goals exact initial_empty masters node d hactive _ (by decide)

end SubexponentialSAT.SubexpNodeCacheReady

end OAI.Algorithms
