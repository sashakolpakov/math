import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutProgram
import OAI.Algorithms.SubexponentialSAT.SubexpMainRows
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowCacheFrames
import OAI.Algorithms.SubexponentialSAT.SubexpMainLagrangeCache

namespace OAI.Algorithms

/-! Actual execution of the cache and row suffix of the layout controller.
The cache arrays and Lagrange dictionary are produced by their fixed
programs. Only the saved outputs of the preceding choices segment are
inputs to this theorem. -/

namespace SubexponentialSAT.SubexpMainLayoutRows

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpLiftRing SubexpQuarticRing
open Subexp.ConstructivePacking

variable {p r Δ D : ℕ} [Fact p.Prime]
variable (xs : List (ZMod p))
variable (P : PackingData (Fin D) (MulticolorTypes.UniversalType r (p^4 - 1) Δ))
variable (scopes : List (List ℕ))

/-- These are precisely the physical outputs used from the choices stage.
All arithmetic cache and workspace facts are produced in this suffix. -/
structure StaticInputs {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : Prop where
  scopes : a.stacks (master alloc 0) = SubexpDenseRowTableProgram.scopesCode scopes
  dimension : a.stacks (master alloc 8) = List.replicate D true
  packing : a.stacks (master alloc 13) =
    SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType
  colors : a.stacks (master alloc 5) = List.replicate r true
  positions : a.stacks (master alloc 6) = List.replicate (p^4 - 1) true
  coefficients : a.stacks (master alloc 9) =
    Subexp.MatrixProgramSupport.words (xs.map (Subexp.MatrixWordEncoding.word p))
  radius : CounterPrograms.value (a.stacks (persistent es 25)) = xs.length

omit [Fact p.Prime] in
theorem StaticInputs.transport {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    (h : StaticInputs xs P scopes alloc a)
    (hm : ∀ i : Fin 32, i ≠ 28 → b.stacks (master alloc i) = a.stacks (master alloc i))
    (hr : b.stacks (persistent es 25) = a.stacks (persistent es 25)) :
    StaticInputs xs P scopes alloc b := by
  constructor
  · exact (hm 0 (by decide)).trans h.scopes
  · exact (hm 8 (by decide)).trans h.dimension
  · exact (hm 13 (by decide)).trans h.packing
  · exact (hm 5 (by decide)).trans h.colors
  · exact (hm 6 (by decide)).trans h.positions
  · exact (hm 9 (by decide)).trans h.coefficients
  · rw [hr]
    exact h.radius

theorem StaticInputs.rowInputs {er es : ℕ} {alloc : Allocation es} {a : MainState er es}
    (h : StaticInputs xs P scopes alloc a) (cache : SubexpMainRowCache.CacheFacts alloc a p) :
    SubexpMainRows.Inputs cache.source xs cache.inverse cache.negative cache.difference P scopes alloc a where
  scopes := h.scopes
  dimension := h.dimension
  packing := h.packing
  colors := h.colors
  positions := h.positions
  coefficients := h.coefficients
  radius := h.radius
  modulus := cache.modulus
  canonicalModulus := cache.canonicalModulus
  reduction := cache.reduction
  width := cache.width
  zero := cache.zero
  zeroBits := cache.zeroBits
  one := cache.one
  minusWidth := cache.minusWidth
  minusValue := cache.minusValue
  inverseArray := cache.inverseArray
  negativeArray := cache.negativeArray
  differenceArray := cache.differenceArray
  nodeWidth := cache.nodeWidth
  inverseWidth := cache.inverseWidth
  negativeWidth := cache.negativeWidth
  differenceWidth := cache.differenceWidth

variable (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

/-- The named intermediate states account for exact measured costs. The
semantic data fields are outputs of the actual suffix execution. -/
structure Result {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a out : MainState er es) where
  firstCache : MainState er es
  secondCache : MainState er es
  afterCache : MainState er es
  afterLagrange : MainState er es
  cache : SubexpMainCacheSetup.Result alloc a afterCache p D
  lagrangeRows : List (List (SubexpMainLagrangeCache.Coefficient p D))
  lagrange : SubexpMainLagrangeCache.Result alloc afterCache afterLagrange
    (SubexpMainLagrangeCache.cacheBytes p D lagrangeRows)
  lagrangeCorrect : SubexpMainLagrangeCache.RowsCorrect p D lagrangeRows
  cacheFacts : SubexpMainRowCache.CacheFacts alloc afterLagrange p
  rows : SubexpMainRows.Result cacheFacts.source xs cacheFacts.inverse cacheFacts.negative
    cacheFacts.difference P scopes hd hr alloc afterLagrange out (D + 1)

noncomputable def runtimeBound {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a out : MainState er es} (h : Result xs P scopes hd hr alloc a out) : ℕ :=
  SubexpMainCacheSetup.runtimeBound alloc a h.firstCache h.secondCache p D +
    SubexpMainLagrangeCache.runtimeBound alloc h.afterCache +
    SubexpMainRows.runtimeBound h.cacheFacts.source xs h.cacheFacts.inverse h.cacheFacts.negative
      h.cacheFacts.difference P scopes hd hr alloc h.afterLagrange (D + 1) + 2

theorem execution {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a : MainState er es) (hstatic : StaticInputs xs P scopes alloc a)
    (hwork : SubexpMainCacheSetup.WorkspaceReady alloc a)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hprecision : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2)
    (hvalid : ∀ C ∈ scopes, ∀ v ∈ C, v < D) (h2 : (2 : ZMod p) ≠ 0) :
    ∃ (out : MainState er es) (h : Result xs P scopes hd hr alloc a out) (n : ℕ),
      n ≤ runtimeBound xs P scopes hd h ∧
      Eval (SubexpMainLayoutProgram.rows er hr alloc).invoke n a out := by
  obtain ⟨b, c, nc, hnc, cached, hec, hc⟩ :=
    SubexpMainCacheSetup.execution alloc a p D hwork hp hprecision hexp
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
  obtain ⟨nr, hnr, out, her, hrow⟩ := SubexpMainRows.execution cache.source xs cache.inverse
    cache.negative cache.difference P scopes hd hr alloc lagged (D + 1)
    (StaticInputs.rowInputs xs P scopes hsLagged cache) hvalid h2 (Nat.zero_lt_succ D) hwidth
  let h : Result xs P scopes hd hr alloc a out := {
    firstCache := b, secondCache := c, afterCache := cached, afterLagrange := lagged
    cache := hc, lagrangeRows := lagrangeRows, lagrange := hl, lagrangeCorrect := hlc
    cacheFacts := cache, rows := hrow }
  refine ⟨out, h, nc + (nl + nr + 1) + 1, ?_, ?_⟩
  · dsimp only [runtimeBound, h]
    omega
  · exact SubexpProcedureCompose.sequence_invoke _ _ hec
      (SubexpProcedureCompose.sequence_invoke _ _ hel her)

theorem Result.persistent_frame {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a out : MainState er es} (h : Result xs P scopes hd hr alloc a out)
    (i : Fin 32) (hi : i ∉ SubexpMainCacheSetup.changedPersistent) :
    out.stacks (persistent es i) = a.stacks (persistent es i) :=
  (SubexpMainRows.Result.persistent_frame h.cacheFacts.source xs h.cacheFacts.inverse
    h.cacheFacts.negative h.cacheFacts.difference P scopes hd h.rows i).trans
    ((h.lagrange.persistent i).trans (h.cache.persistent_frame i hi))

theorem Result.master_frame {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a out : MainState er es} (h : Result xs P scopes hd hr alloc a out)
    (i : Fin 32) (hi : i ≠ 28) : out.stacks (master alloc i) = a.stacks (master alloc i) :=
  (SubexpMainRows.Result.master_frame h.cacheFacts.source xs h.cacheFacts.inverse
    h.cacheFacts.negative h.cacheFacts.difference P scopes hd h.rows i).trans
    ((h.lagrange.master_frame i hi).trans (h.cache.master_frame i))

theorem Result.lagrange_output {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a out : MainState er es} (h : Result xs P scopes hd hr alloc a out) :
    out.stacks (master alloc 28) = SubexpMainLagrangeCache.cacheBytes p D h.lagrangeRows :=
  (SubexpMainRows.Result.master_frame h.cacheFacts.source xs h.cacheFacts.inverse
    h.cacheFacts.negative h.cacheFacts.difference P scopes hd h.rows 28).trans h.lagrange.output

theorem Result.control_frame {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a out : MainState er es} (h : Result xs P scopes hd hr alloc a out)
    (i : Fin 3) : out.regs (controlRegister er i) = a.regs (controlRegister er i) :=
  (SubexpMainRows.Result.control_frame h.cacheFacts.source xs h.cacheFacts.inverse
    h.cacheFacts.negative h.cacheFacts.difference P scopes hd h.rows i).trans
    ((h.lagrange.controls i).trans (h.cache.controls i))

end SubexponentialSAT.SubexpMainLayoutRows

end OAI.Algorithms
