import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheReady
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheTyped
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWideIndex
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWidePipeline
import OAI.Algorithms.SubexponentialSAT.SubexpNodeStoreTransitions

namespace OAI.Algorithms

/-! The first two calls of the fixed node worker. Cache readiness follows
from the actual activated workspace, and the next call computes the node's
rank by searching the physically installed node table. -/

namespace SubexponentialSAT.SubexpNodeCacheIndex

open BitProgram StructuredCalls SubexpLiftRing
open SubexpNodeWorkspace SubexpNodeStoreTransitions

abbrev Data := State 16 288
def ports : Fin 256 → Fin 288 := Fin.castAdd 32
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _
def localState (d : Data) : State 16 256 := projectState id ports d

theorem local_active (masters : Store) (node : List Bool) (d : Data)
    (h : d.stacks = activeStacks masters node) :
    (localState d).stacks = SubexpNodeCacheReady.activeStore masters node := by
  funext i
  exact congrFun h (ports i)

theorem cache_embedded (masters : Store) (node cache : List Bool) (d : Data)
    (hactive : d.stacks = activeStacks masters node) (small : State 16 256)
    (h : small.stacks = Function.update
      (SubexpNodeCacheSetup.preparedStacks (localState d).stacks) 102 cache) :
    (embedState id ports d small).stacks = cached masters node cache := by
  change Function.extend ports small.stacks d.stacks = _
  rw [h]
  simp only [SubexpNodeCacheSetup.preparedStacks,
    ProgramLinking.extend_update ports_injective]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project id ports d Function.injective_id ports_injective)
  change Function.extend ports (localState d).stacks d.stacks = d.stacks at hb
  rw [hb]
  simp only [localState, projectState, Function.comp_apply, hactive]
  rfl

theorem cache_step (p μ : ℕ) [Fact p.Prime]
    (source : SubexpSelectedConversions.Prepared p 0)
    (target : SubexpPreparedQuartic.Modulus p μ) (hμ : 0 < μ)
    (reduction theta : SubexpTaylorRow.Code p μ)
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (R N C : ℕ) (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
    (hC : ∀ row ∈ es, row.length ≤ C)
    (masters : Store) (node : List Bool) (d : Data)
    (hactive : d.stacks = activeStacks masters node)
    (hnode : node = SubexpTaylorRow.flat theta)
    (h5 : masters 5 = target.bits) (h10 : masters 10 = width)
    (h91 : masters 91 = SubexpTaylorRow.flat reduction)
    (h126 : masters 126 = List.replicate N true)
    (h255 : masters 255 = SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat
      (SubexpNodeCacheTyped.rows p μ source R es)) :
    ∃ n ≤ SubexpNodeCacheSetup.prepareCost (localState d) +
      SubexpTaylorCacheMap.tableBudget es.length C (R+1) N (baseWidth p μ) + 1,
      ∃ out : Data, Eval SubexpNodeWidePipeline.cache n d out ∧
      out.stacks = cached masters node
        (SubexpOriginCacheSemantics.taylorBytes p μ source target reduction theta R N es) := by
  have ha := local_active masters node d hactive
  have empty (i : Fin 256) (hi : i ∈ SubexpNodeCacheReady.emptyPorts) :=
    SubexpNodeCacheReady.initial_empty masters node (localState d) ha i hi
  have ready := SubexpNodeCacheReady.prepared_invariant p μ target reduction theta width N
    masters node (localState d) ha hnode h5 h10 h91 h126
  have hm : (localState d).stacks 255 =
      SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat
        (SubexpNodeCacheTyped.rows p μ source R es) := by
    change d.stacks 255 = _
    rw [hactive]
    exact h255
  have hb : (SubexpNodeCacheSetup.width4 width).length = 4 * baseWidth p μ := by
    simp only [SubexpNodeCacheSetup.width4, List.length_append, hw]
    omega
  obtain ⟨n,hn,small,he,hs⟩ := SubexpNodeCacheTyped.command_eval p μ source target
    reduction theta hμ width (SubexpNodeCacheSetup.width4 width) hw hb R N C es hC
    (localState d) (empty 0 (by decide)) (empty 100 (by decide)) (empty 101 (by decide))
    (empty 66 (by decide)) (empty 73 (by decide)) (empty 74 (by decide))
    (empty 81 (by decide)) ready hm (empty 102 (by decide)) (empty 103 (by decide))
    (empty 104 (by decide)) (empty 108 (by decide))
  have ht := compiled_halt_trace he 255 102
  refine ⟨n+1, Nat.add_le_add_right hn 1, embedState id ports d small, ?_,
    cache_embedded masters node _ d hactive small hs⟩
  exact eval_call_from_state SubexpNodeCacheStage.program id ports d
    Function.injective_id ports_injective ht

theorem index_clean (masters : Store) (node cache : List Bool) (d : Data)
    (h : d.stacks = cached masters node cache) :
    SubexpNodeIndexProgram.Clean (SubexpNodeWideIndex.localState d) := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  all_goals
    change d.stacks _ = []
    rw [h]
    rfl

theorem index_step (p D : ℕ) [Fact p.Prime]
    (sourceModulus : SubexpPreparedQuartic.Modulus p 1) (i : Fin (p^4-1))
    (masters : Store) (cache : List Bool) (d : Data)
    (h : d.stacks = cached masters (SubexpNodeIndexSemantics.thetaWord p D i) cache)
    (h125 : masters 125 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) sourceModulus)) :
    ∃ n ≤ SubexpNodeIndexProgram.budget (SubexpNodeIndexSemantics.thetaWord p D i)
      (SubexpNodeLiftData.liftedNodeWords p (D+1) sourceModulus) + 1,
      ∃ out : Data, Eval SubexpNodeWidePipeline.index n d out ∧
      out.stacks = indexed masters (SubexpNodeIndexSemantics.thetaWord p D i)
        cache (List.replicate i.val true) := by
  have hquery : d.stacks 78 = SubexpNodeIndexSemantics.thetaWord p D i := by
    rw [h]
    rfl
  have hmaster : d.stacks 125 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) sourceModulus) := by
    rw [h]
    exact h125
  obtain ⟨n,hn,out,he,hs,_⟩ := SubexpNodeWideIndex.command_eval p D sourceModulus i d
    hquery hmaster (index_clean masters _ cache d h)
  refine ⟨n,hn,out,he,?_⟩
  rw [hs,h]
  rfl

end SubexponentialSAT.SubexpNodeCacheIndex

end OAI.Algorithms
