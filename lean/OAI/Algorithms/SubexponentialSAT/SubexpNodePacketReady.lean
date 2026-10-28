import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeOriginReady
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketLayout

namespace OAI.Algorithms

/-! Actual origin-program output establishes the packet producer's input
layout. The origins and Taylor columns below are computed by the established
row/cache/origin pipeline, rather than supplied as independent tables. -/

namespace SubexponentialSAT.SubexpNodePacketReady

open BitProgram StructuredCalls SubexpLiftRing
open SubexpNodeOriginReady (Data)
open SubexpTaylorCacheMap (encodeList_map_eq)

structure Statics (d : Data) (scopes : List (List ℕ)) (tables : List (List Bool))
    (cache : List (List (List Bool))) (zero one : List Bool) : Prop where
  scopes : d.stacks 256 = Encoding.encodeList SubexpFactorPrefixProgram.scopeBytes scopes
  tables : d.stacks 257 = Encoding.encodeList id tables
  cache : d.stacks 284 = Subexp.FactorPacketCoordinates.cacheBytes cache
  zero : d.stacks 119 = zero
  one : d.stacks 120 = one
  groups : d.stacks 224 = []
  output : d.stacks 225 = []

variable (p μ : ℕ) [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)
variable (target : SubexpPreparedQuartic.Modulus p μ)
variable (reduction theta : SubexpTaylorRow.Code p μ)
variable (R N : ℕ) (hN : 0 < N)
variable (sourceWidth : List Bool) (hw : sourceWidth.length = baseWidth p 1)

def inputs (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
    (scopes : List (List ℕ)) (tables : List (List Bool))
    (cache : List (List (List Bool))) (zero one : List Bool) :
    SubexpFactorPacketProgram.Inputs where
  origins := (SubexpOriginCacheSemantics.origins p μ source target reduction theta R N hN
    source.modulus sourceWidth hw es).map (List.map SubexpFlatLift.encode)
  columns := es.map (List.map (fun e =>
    (SubexpTaylorRowCorrectness.column p μ source target reduction theta R N e).map
      SubexpTaylorRow.flat))
  scopes := scopes
  tables := tables
  cache := cache
  modulus := source.modulus.bits
  zero := zero
  one := one

variable (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
variable (scopes : List (List ℕ)) (tables : List (List Bool))
variable (cache : List (List (List Bool))) (zero one : List Bool)

theorem origins_bytes :
    Encoding.encodeList (Encoding.encodeList id)
      (inputs p μ source target reduction theta R N hN sourceWidth hw es scopes tables cache zero one).origins =
    SubexpNodeOriginExecution.output p μ source target reduction theta R N hN
      source.modulus sourceWidth hw es := by
  change Encoding.encodeList (Encoding.encodeList id)
    ((SubexpOriginCacheSemantics.origins p μ source target reduction theta R N hN
      source.modulus sourceWidth hw es).map (List.map SubexpFlatLift.encode)) = _
  rw [encodeList_map_eq]
  apply congrArg (fun enc => Encoding.encodeList enc
    (SubexpOriginCacheSemantics.origins p μ source target reduction theta R N hN
      source.modulus sourceWidth hw es))
  funext incidence
  exact encodeList_map_eq id SubexpFlatLift.encode incidence

theorem columns_bytes :
    Encoding.encodeList (Encoding.encodeList (Encoding.encodeList id))
      (inputs p μ source target reduction theta R N hN sourceWidth hw es scopes tables cache zero one).columns =
    SubexpOriginCacheSemantics.taylorBytes p μ source target reduction theta R N es := by
  change Encoding.encodeList _ (es.map _) = _
  rw [encodeList_map_eq]
  apply congrArg (fun enc => Encoding.encodeList enc es)
  funext incidence
  rw [encodeList_map_eq]
  apply congrArg (fun enc => Encoding.encodeList enc incidence)
  funext e
  exact encodeList_map_eq id SubexpTaylorRow.flat
    (SubexpTaylorRowCorrectness.column p μ source target reduction theta R N e)

/-- The exact stack equation produced by the origin program discharges
both native input layouts of the subsequent packet program. -/
theorem ready_of_origin_stacks {d out : Data} {inputWidth : List Bool}
    (h : SubexpNodeOriginReady.Ready d source.modulus.bits inputWidth sourceWidth
      (SubexpOriginCacheSemantics.taylorBytes p μ source target reduction theta R N es))
    (s : Statics d scopes tables cache zero one)
    (hs : out.stacks = Function.update d.stacks 227
      (SubexpNodeOriginExecution.output p μ source target reduction theta R N hN
        source.modulus sourceWidth hw es)) :
    SubexpFactorPacketProgram.Ready out
      (inputs p μ source target reduction theta R N hN sourceWidth hw es scopes tables cache zero one) := by
  apply SubexpNodePacketLayout.ready
  constructor
  · simpa only [hs, Function.update_self] using
      (origins_bytes p μ source target reduction theta R N hN sourceWidth hw
        es scopes tables cache zero one).symm
  · simpa only [hs, Function.update_of_ne (by decide : (102 : Fin 288) ≠ 227)] using
      h.cache.trans (columns_bytes p μ source target reduction theta R N hN sourceWidth hw
        es scopes tables cache zero one).symm
  · simpa [hs, inputs] using s.scopes
  · simpa [hs, inputs] using s.tables
  · simpa [hs, inputs] using s.cache
  · simpa [hs, inputs] using h.modulus
  · simpa [hs, inputs] using s.zero
  · simpa [hs, inputs] using s.one
  · intro i hi0 hi1
    have h227 : i ≠ 227 := by intro he; subst i; change 227 < 202 at hi1; omega
    simpa only [hs, Function.update_of_ne h227] using h.work i hi0 hi1
  · simpa [hs] using s.groups
  · simpa [hs] using s.output

/-- No origin table or origin execution is assumed: this invokes the actual
fixed producer, then derives packet readiness from its proved output. -/
theorem origin_command_ready (hμ : 0 < μ) (inputWidth : List Bool)
    (hB : inputWidth.length = baseWidth p μ) (C : ℕ)
    (hC : ∀ incidence ∈ es, incidence.length ≤ C) (d : Data)
    (h : SubexpNodeOriginReady.Ready d source.modulus.bits inputWidth sourceWidth
      (SubexpOriginCacheSemantics.taylorBytes p μ source target reduction theta R N es))
    (s : Statics d scopes tables cache zero one) :
    ∃ n ≤ SubexpOriginMap.tableBound es.length C (baseWidth p μ) (baseWidth p 1)
      source.modulus.bits.length (N - 1), ∃ out : Data,
      Eval SubexpNodeOriginStage.command n d out ∧
      SubexpFactorPacketProgram.Ready out
        (inputs p μ source target reduction theta R N hN sourceWidth hw es scopes tables cache zero one) ∧
      out.stacks = Function.update d.stacks 227
        (SubexpNodeOriginExecution.output p μ source target reduction theta R N hN
          source.modulus sourceWidth hw es) := by
  obtain ⟨n, hn, out, he, hs⟩ := SubexpNodeOriginExecution.command_eval p μ source target
    reduction theta R N hN source.modulus sourceWidth hw hμ inputWidth hB C es hC d
      h.invariant h.cache h.cursor15 h.cursor16 h.accumulator h.output
  exact ⟨n, hn, out, he, ready_of_origin_stacks p μ source target reduction theta R N hN
    sourceWidth hw es scopes tables cache zero one h s hs, hs⟩

end SubexponentialSAT.SubexpNodePacketReady

end OAI.Algorithms
