import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowFrames
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowsProgram
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowProducer

namespace OAI.Algorithms

/-! Main invocation of the concrete dense-row producer. All workspace and
interpreter entry conditions are derived from the executed preparation.
The remaining inputs identify the saved layout records and cache bytes. -/

namespace SubexponentialSAT.SubexpMainRows

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpLiftRing SubexpQuarticRing
open SubexpRowPostfixInterpreter (contextStore)
open SubexpDenseRowTableProgram
open Subexp.ConstructivePacking

attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def prepared {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a : MainState er es) : Data :=
  (row er hr alloc).project (SubexpMainRowPreparation.result alloc a)

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)
variable (xs : List (ZMod p)) (inverse negative : Fin Q → Word)
  (difference : Fin Q → Fin Q → Word)
variable (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
variable (scopes : List (List ℕ))

/-- Readback of the actual retained input records. No row program, row
result, machine trace, or workspace-ready proposition occurs in this record. -/
structure Inputs {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : Prop where
  scopes : a.stacks (master alloc 0) = scopesCode scopes
  dimension : a.stacks (master alloc 8) = List.replicate D true
  packing : a.stacks (master alloc 13) =
    SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType
  colors : a.stacks (master alloc 5) = List.replicate r true
  positions : a.stacks (master alloc 6) = List.replicate Q true
  coefficients : a.stacks (master alloc 9) =
    Subexp.MatrixProgramSupport.words (xs.map (Subexp.MatrixWordEncoding.word p))
  radius : CounterPrograms.value (a.stacks (persistent es 25)) = xs.length
  modulus : a.stacks (ordinary alloc 128) = source.modulus.bits
  canonicalModulus : source.modulus.bits = Subexp.MatrixWordEncoding.modulus p
  reduction : a.stacks (ordinary alloc 130) = SubexpQuarticFlatMul.flat source.reduction
  width : (a.stacks (ordinary alloc 129)).length = baseWidth p 1
  zero : a.stacks (ordinary alloc 131) = SubexpFlatAdd.encode source.zero
  zeroBits : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false
  one : a.stacks (ordinary alloc 132) = SubexpFlatAdd.encode source.one
  minusWidth : (a.stacks (ordinary alloc 133)).length = baseWidth p 1
  minusValue : BinaryArithmetic.toNat (a.stacks (ordinary alloc 133)) = p - 1
  inverseArray : a.stacks (ordinary alloc 135) = (List.ofFn inverse).flatten
  negativeArray : a.stacks (ordinary alloc 136) = (List.ofFn negative).flatten
  differenceArray : a.stacks (ordinary alloc 137) =
    (List.ofFn (fun j => (List.ofFn (difference j)).flatten)).flatten
  nodeWidth : (a.stacks (ordinary alloc 134)).length = Q * (4 * baseWidth p 1)
  inverseWidth : ∀ j, (inverse j).length = 4 * baseWidth p 1
  negativeWidth : ∀ j, (negative j).length = 4 * baseWidth p 1
  differenceWidth : ∀ j k, (difference j k).length = 4 * baseWidth p 1

theorem prepared_masters {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a : MainState er es) (h : Inputs source xs inverse negative difference P scopes alloc a) :
    SubexpGlobalRowInputs.Masters p r Q xs inverse negative difference (prepared hr alloc a) := by
  have hs (i : Fin 10) : (prepared hr alloc a).stacks ⟨128 + i.val, by omega⟩ =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) :=
    SubexpMainRowContext.source_frame alloc a i
  constructor
  · intro j
    exact SubexpMainRowPreparation.result_workspace alloc a j
  · exact SubexpMainRowContext.store_interpreter_empty alloc a 0
  · exact (SubexpMainRowPreparation.result_header alloc a 4).trans h.positions
  · exact (SubexpMainRowPreparation.result_header alloc a 3).trans h.colors
  · change SubexpMainRowContext.store alloc a 243 = _
    rw [SubexpMainRowContext.store_low alloc a 243 (by decide),
      SubexpSourceRowContext.result_dimension]
    simp only [SubexpSourceRowContext.dimension, SubexpMainRowContext.input_radius, h.radius]
  · change ((prepared hr alloc a).stacks 129).length = baseWidth p 1
    exact (congrArg List.length (hs 1)).trans h.width
  · exact (hs 3).trans (h.zero.trans h.zeroBits)
  · change ((prepared hr alloc a).stacks 133).length = baseWidth p 1
    exact (congrArg List.length (hs 5)).trans h.minusWidth
  · exact (congrArg BinaryArithmetic.toNat (hs 5)).trans h.minusValue
  · exact (hs 0).trans (h.modulus.trans h.canonicalModulus)
  · exact (SubexpMainRowPreparation.result_header alloc a 5).trans h.coefficients
  · exact (hs 7).trans h.inverseArray
  · exact (hs 8).trans h.negativeArray
  · exact (hs 9).trans h.differenceArray
  · change ((prepared hr alloc a).stacks 134).length = Q * (4 * baseWidth p 1)
    exact (congrArg List.length (hs 6)).trans h.nodeWidth
  · exact h.inverseWidth
  · exact h.negativeWidth
  · exact h.differenceWidth

theorem prepared_context {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (h : Inputs source xs inverse negative difference P scopes alloc a) :
    SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (xs.length + 1) (a.stacks (ordinary alloc 129))
      (SubexpSourceRowReady.scalarFrame (SubexpMainRowContext.input alloc a))
      (SubexpMainRowContext.context alloc a) := by
  have hc := SubexpMainRowContext.ready alloc a p source.modulus source.reduction source.zero
    h.modulus h.reduction h.width h.zeroBits
  simpa only [h.radius] using hc

variable (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

noncomputable def runtimeBound {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a : MainState er es) (μ : ℕ) : ℕ :=
  SubexpMainRowPreparation.runtimeBound alloc a +
    tableRunCost (prepared hr alloc a)
      (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd)
      (SubexpDenseRowProducer.rowCost μ source xs inverse negative difference P scopes hd
        (prepared hr alloc a)) D scopes + 2

structure Result {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a b : MainState er es) (μ : ℕ) : Prop where
  output : b.stacks (ordinary alloc 255) =
    tableCode (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd) D scopes
  consumed : ∀ i ∈ ([256, 264, 265] : List (Fin 288)),
    b.stacks (ordinary alloc ⟨i.val, by omega⟩) = []
  nativeFrame : ∀ i : Fin 288, i ≠ 255 → i ≠ 256 → i ≠ 264 → i ≠ 265 →
    b.stacks (ordinary alloc ⟨i.val, by omega⟩) =
      (SubexpMainRowPreparation.result alloc a).stacks (ordinary alloc ⟨i.val, by omega⟩)
  externalFrame : ∀ i : Fin (totalStacks es), 288 ≤ i.val →
    b.stacks i = (SubexpMainRowPreparation.result alloc a).stacks i
  controls : ∀ i, b.regs (controlRegister er i) =
    (SubexpMainRowPreparation.result alloc a).regs (controlRegister er i)

/-- Complete measured execution. The concrete source/lookup/evaluation row
service is instantiated internally, after the actual preparation program. -/
theorem execution {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a : MainState er es) (μ : ℕ)
    (h : Inputs source xs inverse negative difference P scopes alloc a)
    (hvalid : ∀ C ∈ scopes, ∀ v ∈ C, v < D)
    (h2 : (2 : ZMod p) ≠ 0) (hμ : 0 < μ)
    (hB : (a.stacks (persistent es 13)).length = baseWidth p μ) :
    ∃ n ≤ runtimeBound source xs inverse negative difference P scopes hd hr alloc a μ, ∃ b,
      Eval (procedure er hr alloc).invoke n a b ∧
      Result source xs inverse negative difference P scopes hd hr alloc a b μ := by
  let d := prepared hr alloc a
  have hm := prepared_masters source xs inverse negative difference P scopes hr alloc a h
  have hp : d.stacks 265 = SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType :=
    (SubexpMainRowPreparation.result_header alloc a 2).trans h.packing
  have hs : d.stacks 256 = SubexpIncidenceSlotProgram.scopeBits scopes :=
    (SubexpMainRowPreparation.result_header alloc a 0).trans h.scopes
  have hz : d.stacks 131 = SubexpFlatAdd.encode source.zero :=
    (SubexpMainRowContext.source_frame alloc a 3).trans h.zero
  have ho : d.stacks 132 = SubexpFlatAdd.encode source.one :=
    (SubexpMainRowContext.source_frame alloc a 4).trans h.one
  have hf (j : Fin 256) : d.stacks (SubexpRowToTaylorCalls.stack j) =
      contextStore (SubexpMainRowContext.context alloc a) j := by
    exact (congrFun (SubexpMainRowContext.contextStore_eq alloc a) j).symm
  obtain ⟨rf, nt, hnt, ht⟩ := SubexpDenseRowProducer.program_runsIn μ source xs inverse negative difference
    P scopes hd d hvalid h2 hμ hm hp hs
    (SubexpMainRowPreparation.high_clean alloc a)
    (SubexpMainRowPreparation.result_zero87 alloc a) hz ho
    (a.stacks (ordinary alloc 129)) (a.stacks (persistent es 13))
    (SubexpSourceRowReady.scalarFrame (SubexpMainRowContext.input alloc a))
    (SubexpMainRowContext.context alloc a)
    (prepared_context source xs inverse negative difference P scopes alloc a h) h.zeroBits
    (SubexpMainRowContext.target_width alloc a) (SubexpMainRowContext.output_empty alloc a) hB hf
    (SubexpMainRowPreparation.table_ready alloc a D scopes d.regs h.scopes h.dimension)
  let render := SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd
  let out := tableResult d rf render D scopes
  let b := (row er hr alloc).install (SubexpMainRowPreparation.result alloc a) out
  obtain ⟨np, hnp, hprep⟩ := SubexpMainRowPreparation.execution alloc a
  have hrow : Eval (row er hr alloc).invoke nt (SubexpMainRowPreparation.result alloc a) b :=
    Procedure.invoke_trace _ _ _ ht
  refine ⟨np + nt + 1, ?_, b, SubexpProcedureCompose.sequence_invoke _ _ hprep hrow, ?_⟩
  · dsimp [runtimeBound]
    dsimp only [d] at hnt
    omega
  · have hb (i : Fin 288) : b.stacks (ordinary alloc ⟨i.val, by omega⟩) = out.stacks i :=
      embedState_stack (row er hr alloc).registerMap (row er hr alloc).stack
        (SubexpMainRowPreparation.result alloc a) out (row er hr alloc).stack.injective i
    constructor
    · exact (hb 255).trans (tableResult_output d rf render D scopes)
    · intro i hi
      rw [hb]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> simp [out, tableResult]
    · intro i h255 h256 h264 h265
      exact (hb i).trans (tableResult_frame d rf render D scopes i h255 h256 h264 h265)
    · intro i hi
      apply embedState_stack_frame
      rintro ⟨j, he⟩
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
      change j.val = i.val at hv
      have hj := j.isLt
      change j.val < 288 at hj
      omega
    · exact Procedure.install_control _ _ _

theorem Result.persistent_frame {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a b : MainState er es} {μ : ℕ}
    (h : Result source xs inverse negative difference P scopes hd hr alloc a b μ)
    (i : Fin 32) : b.stacks (persistent es i) = a.stacks (persistent es i) := by
  have hw := alloc.enough.trans alloc.within
  exact (h.externalFrame _ (by change 288 ≤ workStacks es + i.val; omega)).trans
    (SubexpMainRowPreparation.result_persistent alloc a i)

theorem Result.master_frame {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a b : MainState er es} {μ : ℕ}
    (h : Result source xs inverse negative difference P scopes hd hr alloc a b μ)
    (i : Fin 32) : b.stacks (master alloc i) = a.stacks (master alloc i) :=
  (h.externalFrame _ (by rw [SubexpLayoutPorts.master_val]; omega)).trans
    (SubexpMainRowPreparation.result_master alloc a i)

theorem Result.threshold_frame {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a b : MainState er es} {μ : ℕ}
    (h : Result source xs inverse negative difference P scopes hd hr alloc a b μ)
    (i : Fin (totalStacks es)) (hlo : alloc.ordinaryCount ≤ i.val)
    (hhi : i.val < workStacks es) : b.stacks i = a.stacks i :=
  (h.externalFrame i (by have := alloc.enough; omega)).trans
    (SubexpMainRowPreparation.result_threshold alloc a i hlo hhi)

theorem Result.control_frame {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a b : MainState er es} {μ : ℕ}
    (h : Result source xs inverse negative difference P scopes hd hr alloc a b μ)
    (i : Fin 3) : b.regs (controlRegister er i) = a.regs (controlRegister er i) :=
  (h.controls i).trans (SubexpMainRowPreparation.result_control alloc a i)

theorem Result.source_frame {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a b : MainState er es} {μ : ℕ}
    (h : Result source xs inverse negative difference P scopes hd hr alloc a b μ)
    (i : Fin 10) :
    b.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) := by
  let j : Fin 288 := ⟨128 + i.val, by omega⟩
  have ne (k : Fin 288) (hk : 138 ≤ k.val) : j ≠ k := by
    intro he
    have hv := congrArg (fun q : Fin 288 => q.val) he
    change 128 + i.val = k.val at hv
    omega
  exact (h.nativeFrame j (ne 255 (by decide)) (ne 256 (by decide))
    (ne 264 (by decide)) (ne 265 (by decide))).trans
    (SubexpMainRowContext.source_frame alloc a i)

end SubexponentialSAT.SubexpMainRows

end OAI.Algorithms
