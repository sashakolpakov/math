import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutPattern
import OAI.Algorithms.SubexponentialSAT.SubexpMainOrderedReconstruction

namespace OAI.Algorithms

/-!
# The factor system at the physical layout dimension

The encoded dimension is connected to the chunk count by a proved equality.
The numeric system retains the exact emitted factor order and original
tables. Reconstructing with it uses the actual numeric CRT trace.
-/

namespace SubexponentialSAT.SubexpMainPhysicalSystem

open StructuredCalls SubexpMainProgram SubexpSetupProgram SubexpLayoutSpec
open SubexpMainLayoutInput

variable {n ell D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]

noncomputable def system (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hD : D = ChunkPartition.count n ell) :
    Factor.System (Fin D) (Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) (ZMod p) :=
  hD.symm ▸ Subexp.OrderedScopeSystem.system
    (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G))
    (SubexpLeafData.factors G hG)
    (SubexpLeafData.scopes G hG (ChunkPartition.indexEquiv n ell hell))
    (SubexpLeafData.scopes_mem G hG (ChunkPartition.indexEquiv n ell hell)
      (PackedSAT.capacity (n := n) hcap))

theorem system_toPattern (G : SubexpLeafData.Leaf n)
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hD : D = ChunkPartition.count n ell) :
    (system G hG hell hcap hD).toPattern =
      Subexp.IncidencePlanSpec.pattern D (SubexpLeafScopeOrder.rawScopes G hG hell) := by
  cases hD
  rfl

/-- Only the proved equality of patterns is used. All rows, nodes, supports,
and subspaces still come from the supplied actual layout. -/
noncomputable def layout (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hD : D = ChunkPartition.count n ell)
    {c : Parameters p k Δ r tau}
    (L : Layout (E := SubexpActualRing.E p)
      (Subexp.IncidencePlanSpec.pattern D (SubexpLeafScopeOrder.rawScopes G hG hell)) c) :
    Layout (E := SubexpActualRing.E p) (system G hG hell hcap hD).toPattern c :=
  (system_toPattern G hG hell hcap hD).symm ▸ L

theorem complete {cfg : Config} {er occ : ℕ}
    (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hD : D = ChunkPartition.count n ell)
    (hk : 1 ≤ k) (sparse : SubexpLeafSemantics.Sparse k occ G)
    (hne : [] ∉ G) (hdelta : 1 + ell * occ ≤ Δ)
    {c : Parameters p k Δ r tau}
    (L : Layout (E := SubexpActualRing.E p)
      (Subexp.IncidencePlanSpec.pattern D (SubexpLeafScopeOrder.rawScopes G hG hell)) c)
    (alloc : SubexpMainCRT.Allocation (mainExtraStacks cfg))
    (halloc : alloc.ordinaryCount = helperSize cfg)
    (phases : Phases er (mainExtraStacks cfg))
    (hcrt : phases.crt = SubexpMainCRT.procedure er alloc)
    (start afterLayout afterMoments : MainState er (mainExtraStacks cfg))
    (layoutSteps momentSteps : ℕ)
    (layoutTrace : Eval phases.layout.invoke layoutSteps (transferredData start) afterLayout)
    (momentTrace : Eval phases.moments.invoke momentSteps afterLayout afterMoments)
    (input : SubexpMainSystemReadback.Readback (system G hG hell hcap hD)
      (layout G hG hell hcap hD L) alloc afterMoments)
    {setup : SetupState cfg} {cacheSize : ℕ}
    (stored : SubexpMainInvariant.Stored cfg setup cacheSize afterMoments)
    (sourceFrame : afterMoments.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 7) =
      (transferredData start).stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 7))
    (payloadFrame : afterMoments.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 8) =
      (transferredData start).stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 8))
    (leafFrame : afterMoments.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9) =
      (transferredData start).stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9))
    (hn : 0 < n) :
    ∃ original : Layout (E := SubexpActualRing.E p)
        (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern c,
      ∃ stages : SubexpLeafContract.ReconstructionStages phases G hell hcap original start,
        stages.prefixSteps ≤ layoutSteps + momentSteps + input.bound ∧
        SubexpMainInvariant.Stored cfg setup cacheSize stages.afterCRT := by
  cases hD
  have hb := SubexpLEFactorSystem.packed_bounded hell hcap (ExecCNF.formulaSet G)
    hk sparse.width sparse.occurrences (SubexpLeafData.clauses_nonempty G hne)
  have hP : (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern.Bounded k Δ :=
    ⟨hb.nonempty_scope, hb.arity_le, fun v => (hb.incidence_le v).trans hdelta⟩
  obtain ⟨stages, hbound, hstored⟩ := SubexpMainOrderedReconstruction.complete G hell hcap
    (SubexpLeafData.factors G hG)
    (SubexpLeafData.scopes G hG (ChunkPartition.indexEquiv n ell hell))
    (SubexpLeafData.scopes_mem G hG (ChunkPartition.indexEquiv n ell hell)
      (PackedSAT.capacity (n := n) hcap)) hP L alloc halloc phases hcrt
    start afterLayout afterMoments layoutSteps momentSteps layoutTrace momentTrace
    input stored sourceFrame payloadFrame leafFrame hn
  exact ⟨_, stages, hbound, hstored⟩

/-- Equality transport back to the caller's original leaf and chunk width
preserves every physical output state and the measured prefix cost. -/
theorem cast_back {er es m ell' : ℕ} (G : SubexpLeafData.Leaf n)
    (hN : n = m) (hEll : ell = ell') (hell : 0 < ell) (hcap : 2 ^ ell ≤ p)
    (hell' : 0 < ell') (hcap' : 2 ^ ell' ≤ p)
    {c : Parameters p k Δ r tau} (phases : Phases er es) (start : MainState er es)
    (L : Layout (E := SubexpActualRing.E p)
      (SubexpLEFactorSystem.packed hell' hcap'
        (ExecCNF.formulaSet (castLeaf hN G))).toPattern c)
    (stages : SubexpLeafContract.ReconstructionStages phases (castLeaf hN G)
      hell' hcap' L start) :
    ∃ original : Layout (E := SubexpActualRing.E p)
        (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern c,
      ∃ result : SubexpLeafContract.ReconstructionStages phases G hell hcap original start,
        result.afterLayout = stages.afterLayout ∧ result.afterMoments = stages.afterMoments ∧
        result.afterCRT = stages.afterCRT ∧ result.prefixSteps = stages.prefixSteps := by
  cases hN
  cases hEll
  exact ⟨L, stages, rfl, rfl, rfl, rfl⟩

end SubexponentialSAT.SubexpMainPhysicalSystem

end OAI.Algorithms
