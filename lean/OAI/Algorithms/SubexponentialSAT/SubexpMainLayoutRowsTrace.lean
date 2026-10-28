import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutRows
import OAI.Algorithms.SubexponentialSAT.SubexpMainCacheSetupTrace

namespace OAI.Algorithms

/-!
# Actual intermediate traces for the layout row suffix

The named cache and Lagrange states in the existing result record are tied
to their actual bounded calls.  The row-input facts are derived along that
same execution.  No intermediate state-size bound is a premise.
-/

namespace SubexponentialSAT.SubexpMainLayoutRowsTrace

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpLiftRing SubexpQuarticRing
open Subexp.ConstructivePacking SubexpMainLayoutRows
open SubexpMainCacheSetupTrace (Run)

variable {p r Δ D : ℕ} [Fact p.Prime]
variable (xs : List (ZMod p))
variable (P : PackingData (Fin D) (MulticolorTypes.UniversalType r (p^4 - 1) Δ))
variable (scopes : List (List ℕ))
variable (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

structure StageTrace {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a out : MainState er es} (h : Result xs P scopes hd hr alloc a out) : Prop where
  cacheTrace : SubexpMainCacheSetupTrace.StageTrace alloc a h.firstCache h.secondCache
    h.afterCache p D
  cacheRun : Run (SubexpMainCacheSetup.procedure er alloc)
    (SubexpMainCacheSetup.runtimeBound alloc a h.firstCache h.secondCache p D) a h.afterCache
  cachedStatic : StaticInputs xs P scopes alloc h.afterCache
  lagrangeRun : Run (SubexpMainLagrangeCache.procedure er alloc)
    (SubexpMainLagrangeCache.runtimeBound alloc h.afterCache) h.afterCache h.afterLagrange
  laggedStatic : StaticInputs xs P scopes alloc h.afterLagrange
  rowInputs : SubexpMainRows.Inputs h.cacheFacts.source xs h.cacheFacts.inverse
    h.cacheFacts.negative h.cacheFacts.difference P scopes alloc h.afterLagrange
  rowsRun : Run (SubexpMainRows.procedure er hr alloc)
    (SubexpMainRows.runtimeBound h.cacheFacts.source xs h.cacheFacts.inverse h.cacheFacts.negative
      h.cacheFacts.difference P scopes hd hr alloc h.afterLagrange (D + 1)) h.afterLagrange out

theorem execution {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a : MainState er es) (hstatic : StaticInputs xs P scopes alloc a)
    (hwork : SubexpMainCacheSetup.WorkspaceReady alloc a)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hprecision : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2)
    (hvalid : ∀ C ∈ scopes, ∀ v ∈ C, v < D) (h2 : (2 : ZMod p) ≠ 0) :
    ∃ (out : MainState er es) (h : Result xs P scopes hd hr alloc a out) (n : ℕ),
      n ≤ runtimeBound xs P scopes hd h ∧
      Eval (SubexpMainLayoutProgram.rows er hr alloc).invoke n a out ∧
      StageTrace xs P scopes hd h := by
  obtain ⟨b, c, nc, hnc, cached, hec, hc, hct⟩ :=
    SubexpMainCacheSetupTrace.execution alloc a p D hwork hp hprecision hexp
  obtain ⟨nl, hnl, lagged, lagrangeRows, hel, hl, hlc⟩ :=
    SubexpMainLagrangeCache.execution alloc a cached p D hc hp hprecision hexp
  let cache := SubexpMainRowCache.CacheFacts.transport
    (SubexpMainRowCache.of_result hc) hl.source_frame
  have hsCached : StaticInputs xs P scopes alloc cached :=
    StaticInputs.transport xs P scopes hstatic (fun i _ => hc.master_frame i)
      (hc.persistent_frame 25 (by decide))
  have hsLagged : StaticInputs xs P scopes alloc lagged :=
    StaticInputs.transport xs P scopes hsCached hl.master_frame (hl.persistent 25)
  have hwidth : (lagged.stacks (persistent es 13)).length = baseWidth p (D + 1) :=
    (congrArg List.length (hl.persistent 13)).trans hc.target_lengths.2.1
  have hrowInputs := StaticInputs.rowInputs xs P scopes hsLagged cache
  obtain ⟨nr, hnr, out, her, hrow⟩ := SubexpMainRows.execution cache.source xs cache.inverse
    cache.negative cache.difference P scopes hd hr alloc lagged (D + 1)
    hrowInputs hvalid h2 (Nat.zero_lt_succ D) hwidth
  let h : Result xs P scopes hd hr alloc a out := {
    firstCache := b, secondCache := c, afterCache := cached, afterLagrange := lagged
    cache := hc, lagrangeRows := lagrangeRows, lagrange := hl, lagrangeCorrect := hlc
    cacheFacts := cache, rows := hrow }
  have ht : StageTrace xs P scopes hd h := {
    cacheTrace := hct
    cacheRun := ⟨nc, hnc, hec⟩
    cachedStatic := hsCached
    lagrangeRun := ⟨nl, hnl, hel⟩
    laggedStatic := hsLagged
    rowInputs := hrowInputs
    rowsRun := ⟨nr, hnr, her⟩ }
  refine ⟨out, h, nc + (nl + nr + 1) + 1, ?_, ?_, ht⟩
  · dsimp only [runtimeBound, h]
    omega
  · exact SubexpProcedureCompose.sequence_invoke _ _ hec
      (SubexpProcedureCompose.sequence_invoke _ _ hel her)

end SubexponentialSAT.SubexpMainLayoutRowsTrace

end OAI.Algorithms
