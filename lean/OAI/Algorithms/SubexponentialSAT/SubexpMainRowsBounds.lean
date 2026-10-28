import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainRows
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowProducerBound

namespace OAI.Algorithms

/-!
# Concrete polynomial bound for the Main row phase

The native producer bound is reconstructed from the input caches and saved
layout records after the actual preparation. Preparation retains its measured
cost, including the real clearing of old selected workspace contents.
-/

namespace SubexponentialSAT.SubexpMainRowsBounds

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpLiftRing SubexpQuarticRing SubexpDenseRowTableProgram
open Subexp.ConstructivePacking

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The native source-size expression read directly from saved input words.
Cleared parser words and old row accumulators do not occur in this list. -/
def inputSourceSize {er es : ℕ} (p r Q Δ R : ℕ) (alloc : Allocation es)
    (a : MainState er es) : ℕ :=
  r + Q + Δ + R + Subexp.MatrixWordEncoding.width p +
    Subexp.CollisionProgram.typeWidth r Q Δ +
    [(a.stacks (ordinary alloc 128)).length, (a.stacks (ordinary alloc 129)).length,
      (a.stacks (ordinary alloc 131)).length, (a.stacks (ordinary alloc 132)).length,
      (a.stacks (ordinary alloc 133)).length, (a.stacks (ordinary alloc 134)).length,
      (a.stacks (ordinary alloc 135)).length, (a.stacks (ordinary alloc 136)).length,
      (a.stacks (ordinary alloc 137)).length, R + 1,
      (a.stacks (master alloc 5)).length, (a.stacks (master alloc 6)).length,
      (a.stacks (master alloc 9)).length].sum + 1

/-- Explicit input-word version of the native producer polynomial. The
separate Main preparation cost is deliberately not folded into this bound. -/
def inputRuntimeBound {er es : ℕ} (p r Q Δ D μ R : ℕ) (scopes : List (List ℕ))
    (alloc : Allocation es) (a : MainState er es) : ℕ :=
  let K := Subexp.UniversalRowAssemblyBound.uniformBound (inputSourceSize p r Q Δ R alloc a) + 1
  let L := (a.stacks (master alloc 13)).length
  tablePolynomialBound (scopesCode scopes).length D
    (SubexpDenseRowServiceBound.serviceBound D (Subexp.CollisionProgram.typeWidth r Q Δ)
      R (baseWidth p 1) (baseWidth p μ) L
      (SubexpIncidenceSlotProgram.scopeBits scopes).length scopes.length K K)
    (SubexpDenseRowServiceBound.rowLength p μ R) L

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)
variable (xs : List (ZMod p)) (inverse negative : Fin Q → Word)
  (difference : Fin Q → Fin Q → Word)
variable (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
variable (scopes : List (List ℕ))

theorem sourceSize_input {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a : MainState er es)
    (h : SubexpMainRows.Inputs source xs inverse negative difference P scopes alloc a) :
    SubexpDenseRowProducerBound.sourceSize p r Q Δ xs.length (SubexpMainRows.prepared hr alloc a) =
      inputSourceSize p r Q Δ xs.length alloc a := by
  let d := SubexpMainRows.prepared hr alloc a
  have hs (i : Fin 10) : d.stacks ⟨128 + i.val, by omega⟩ =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) :=
    SubexpMainRowContext.source_frame alloc a i
  have hm := SubexpMainRows.prepared_masters source xs inverse negative difference P scopes hr alloc a h
  have h243 : d.stacks 243 = List.replicate (xs.length + 1) true := hm.degree
  have h252 : d.stacks 252 = a.stacks (master alloc 5) :=
    SubexpMainRowPreparation.result_header alloc a 3
  have h253 : d.stacks 253 = a.stacks (master alloc 6) :=
    SubexpMainRowPreparation.result_header alloc a 4
  have h254 : d.stacks 254 = a.stacks (master alloc 9) :=
    SubexpMainRowPreparation.result_header alloc a 5
  have h128 : d.stacks 128 = a.stacks (ordinary alloc 128) := hs 0
  have h129 : d.stacks 129 = a.stacks (ordinary alloc 129) := hs 1
  have h131 : d.stacks 131 = a.stacks (ordinary alloc 131) := hs 3
  have h132 : d.stacks 132 = a.stacks (ordinary alloc 132) := hs 4
  have h133 : d.stacks 133 = a.stacks (ordinary alloc 133) := hs 5
  have h134 : d.stacks 134 = a.stacks (ordinary alloc 134) := hs 6
  have h135 : d.stacks 135 = a.stacks (ordinary alloc 135) := hs 7
  have h136 : d.stacks 136 = a.stacks (ordinary alloc 136) := hs 8
  have h137 : d.stacks 137 = a.stacks (ordinary alloc 137) := hs 9
  change SubexpDenseRowProducerBound.sourceSize p r Q Δ xs.length d = _
  simp only [SubexpDenseRowProducerBound.sourceSize, SubexpDenseRowProducerBound.sourceMasterPorts,
    List.map_cons, List.map_nil, h128, h129, h131, h132, h133, h134, h135, h136, h137,
    h243, h252, h253, h254, List.length_replicate, inputSourceSize]

theorem nativeRuntimeBound_input {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a : MainState er es) (μ : ℕ)
    (h : SubexpMainRows.Inputs source xs inverse negative difference P scopes alloc a) :
    SubexpDenseRowProducerBound.runtimeBound p r Q Δ D μ xs.length scopes
      (SubexpMainRows.prepared hr alloc a) = inputRuntimeBound p r Q Δ D μ xs.length scopes alloc a := by
  have hp : (SubexpMainRows.prepared hr alloc a).stacks 265 = a.stacks (master alloc 13) :=
    SubexpMainRowPreparation.result_header alloc a 2
  simp only [SubexpDenseRowProducerBound.runtimeBound, SubexpDenseRowProducerBound.tableBudget,
    SubexpDenseRowServiceBound.uniformRowBound, SubexpDenseRowProducerBound.sourceLimit,
    sourceSize_input source xs inverse negative difference P scopes hr alloc a h,
    hp, inputRuntimeBound]

variable (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

/-- The measured Main phase is bounded by actual preparation plus the
closed native polynomial. The final `+1` is the procedure sequence step. -/
theorem runtimeBound_le {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a : MainState er es) (μ : ℕ)
    (h : SubexpMainRows.Inputs source xs inverse negative difference P scopes alloc a)
    (h2 : (2 : ZMod p) ≠ 0) :
    SubexpMainRows.runtimeBound source xs inverse negative difference P scopes hd hr alloc a μ ≤
      SubexpMainRowPreparation.runtimeBound alloc a +
        SubexpDenseRowProducerBound.runtimeBound p r Q Δ D μ xs.length scopes
          (SubexpMainRows.prepared hr alloc a) + 1 := by
  let d := SubexpMainRows.prepared hr alloc a
  have hm := SubexpMainRows.prepared_masters source xs inverse negative difference P scopes hr alloc a h
  have hp : d.stacks 265 = SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType :=
    (SubexpMainRowPreparation.result_header alloc a 2).trans h.packing
  have hz : d.stacks 131 = SubexpFlatAdd.encode source.zero :=
    (SubexpMainRowContext.source_frame alloc a 3).trans h.zero
  have ho : d.stacks 132 = SubexpFlatAdd.encode source.one :=
    (SubexpMainRowContext.source_frame alloc a 4).trans h.one
  have ha : TableReady d D scopes :=
    SubexpMainRowPreparation.table_ready alloc a D scopes d.regs h.scopes h.dimension
  have hn := SubexpDenseRowProducerBound.tableRunCost_le μ source xs inverse negative difference
    P scopes hd d h2 hm hp hz ho ha
  dsimp only [d] at hn
  unfold SubexpMainRows.runtimeBound
  omega

/-- Input-word form: only the explicitly measured preparation term charges
old selected workspace contents. The native polynomial reads saved data. -/
theorem runtimeBound_le_input {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a : MainState er es) (μ : ℕ)
    (h : SubexpMainRows.Inputs source xs inverse negative difference P scopes alloc a)
    (h2 : (2 : ZMod p) ≠ 0) :
    SubexpMainRows.runtimeBound source xs inverse negative difference P scopes hd hr alloc a μ ≤
      SubexpMainRowPreparation.runtimeBound alloc a +
        inputRuntimeBound p r Q Δ D μ xs.length scopes alloc a + 1 := by
  have hb := runtimeBound_le source xs inverse negative difference P scopes hd hr alloc a μ h h2
  rw [nativeRuntimeBound_input source xs inverse negative difference P scopes hr alloc a μ h] at hb
  exact hb

end SubexponentialSAT.SubexpMainRowsBounds

end OAI.Algorithms
