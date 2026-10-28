import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutEnumeration
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentData
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBlueprintWorkspace

namespace OAI.Algorithms

/-!
# Static node inputs from the actual Main outputs

The basis and packet masters below are consequences of the layout result,
the actual node initialization, and its scratch-clear frame. The node's
local tables are selected from the emitted batch at the literal node index.
No static-input contract or replacement table is assumed.
-/

noncomputable section

namespace SubexponentialSAT.SubexpMainMomentStatics

open SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation master)
open SubexpMainLayoutEnumeration (context)
open SubexpMainMomentData (store target)

variable {er es p r Δ R D : ℕ} [Fact p.Prime] [NeZero r]
variable {alloc : Allocation es} {a middle out b : MainState er es}
variable {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p^4 - 1}
variable {scopes : List (List ℕ)}
variable {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
variable {tables : List (List Bool)}
variable (h : SubexpMainLayoutExecution.Result hregs alloc a middle out
  p r Δ R D hr hQ scopes hd tables)
variable (hi : SubexpMainNodeInitialization.Result alloc
  (SubexpMainNodeSetup.prepared alloc out) b D)

def nodeBatches : List (List Bool) := List.ofFn (fun t => (context h t).batch)

def before (t : Fin (p^4 - 1)) : List (List Bool) := (nodeBatches h).take t.val

def after (t : Fin (p^4 - 1)) : List Bool :=
  ProgramEncoding.encodeRecords ((nodeBatches h).drop (t.val + 1))

theorem nodeBatches_length : (nodeBatches h).length = p^4 - 1 := List.length_ofFn

theorem before_length (t : Fin (p^4 - 1)) : (before h t).length = t.val := by
  rw [before, List.length_take, nodeBatches_length]
  exact Nat.min_eq_left t.isLt.le

include h hi in
theorem scalar_master (i : Fin 7) :
    store alloc b ⟨256 + (21 + i.val), by omega⟩ = SubexpMainScalarAlphabet.targetWord p i := by
  have hj : (⟨21 + i.val, by omega⟩ : Fin 32) ≠ 28 := by
    intro he
    have hv := congrArg Fin.val he
    change 21 + i.val = 28 at hv
    omega
  exact (SubexpMainMomentData.static_frame hi ⟨21 + i.val, by omega⟩).trans
    ((h.saved_master _ hj).trans (h.choices.scalar i))

include hi in
theorem batch_word : store alloc b 270 = ProgramEncoding.encodeRecords (nodeBatches h) :=
  (SubexpMainMomentData.static_frame hi 14).trans
    (SubexpMainLayoutEnumeration.basis_master h)

include hi in
theorem batch_split (t : Fin (p^4 - 1)) : store alloc b 270 =
    GlobalBasisRecordLookup.recordsPrefix (before h t) ++
      GlobalBasisRecordLookup.record (context h t).batch ++ after h t := by
  rw [batch_word h hi]
  have ht : t.val < (nodeBatches h).length := by
    rw [nodeBatches_length]
    exact t.isLt
  have hs := GlobalBasisInput.encode_get (nodeBatches h) t.val ht
  simpa only [ProgramEncoding.encodeRecords, before, after, nodeBatches,
    List.getElem_ofFn] using hs

include hi in
/-- All retained basis inputs, including the actual batch split, follow
from the producing stages and the physical static-storage frame. -/
theorem basis_masters (t : Fin (p^4 - 1)) :
    SubexpNodeBasisWorkspace.Masters (context h t)
      h.choices.packing.packing.blockCount h.choices.packing.packing.leftovers.length D
      (before h t) (after h t) (store alloc b) := by
  constructor
  · exact (SubexpMainMomentData.static_frame hi 20).trans
      ((h.saved_master 20 (by decide)).trans h.choices.scalarWidth)
  · exact scalar_master h hi 5
  · exact scalar_master h hi 6
  · exact (SubexpMainMomentData.static_frame hi 13).trans
      (SubexpMainLayoutEnumeration.metadata_master h)
  · exact (SubexpMainMomentData.static_frame hi 10).trans
      ((h.saved_master 10 (by decide)).trans h.choices.prefixResult.universal)
  · exact (SubexpMainMomentData.static_frame hi 5).trans
      ((h.saved_master 5 (by decide)).trans (h.choices.prefixResult.headers 0))
  · exact batch_split h hi t
  · exact before_length h t
  · exact (SubexpMainMomentData.static_frame hi 8).trans (SubexpMainMomentData.layout_dimension h)
  · exact (SubexpMainMomentData.static_frame hi 15).trans (h.packing_master 0)
  · exact (SubexpMainMomentData.static_frame hi 16).trans (h.packing_master 1)
  · exact scalar_master h hi 2
  · exact scalar_master h hi 0
  · have hs := scalar_master h hi 3
    change store alloc b 280 = ProgramEncoding.encodeRecords (ScalarSetupProgram.tokenAlphabet p) at hs
    simpa only [SubexpMainScalarAlphabet.tokenAlphabet_eq_tokens] using hs

include hi in
theorem exists_basis_masters (t : Fin (p^4 - 1)) :
    ∃ before tail, SubexpNodeBasisWorkspace.Masters (context h t)
      h.choices.packing.packing.blockCount h.choices.packing.packing.leftovers.length D
      before tail (store alloc b) :=
  ⟨before h t, after h t, basis_masters h hi t⟩

/-- The exact flat-quartic rows retained by the Lagrange producer. -/
def lagrange : List (List (List Bool)) :=
  h.rows.lagrangeRows.map (List.map SubexpQuarticFlatNeg.flat)

theorem lagrange_encoding :
    SubexpLagrangeCacheLoop.encodeRows p (D + 1) h.rows.lagrangeRows = lagrange h := by
  have he : (SubexpFlatAdd.encode : SubexpMainLagrangeCache.Coefficient p D → List Bool) =
      SubexpQuarticFlatNeg.flat := by
    funext x
    exact (SubexpMainRowCache.flat_eq_encode x).symm
  simp only [SubexpLagrangeCacheLoop.encodeRows, lagrange, he]
  rfl

include hi in
theorem lagrange_word : store alloc b 284 = FactorPacketCoordinates.cacheBytes (lagrange h) := by
  have hl := (SubexpMainMomentData.static_frame hi 28).trans
    (SubexpMainLayoutRows.Result.lagrange_output (List.ofFn h.choices.coefficients)
      h.choices.packing.packing scopes hd h.rows)
  change store alloc b 284 = FactorPacketCoordinates.cacheBytes
    (SubexpLagrangeCacheLoop.encodeRows p (D + 1) h.rows.lagrangeRows) at hl
  rw [lagrange_encoding h] at hl
  exact hl

include hi in
/-- Packet inputs are the actual scope, factor-table, Lagrange and target
constant words preserved into the node worker. -/
theorem packet_masters :
    SubexpNodeBlueprintWorkspace.PacketMasters (store alloc b) scopes tables (lagrange h)
      (SubexpQuarticFlatNeg.flat (target p D).zero)
      (SubexpQuarticFlatNeg.flat (target p D).one) := by
  constructor
  · exact (SubexpMainMomentData.static_frame hi 0).trans h.scope_master
  · exact (SubexpMainMomentData.static_frame hi 1).trans h.table_master
  · exact lagrange_word h hi
  · exact SubexpMainMomentData.target_zero h hi
  · exact SubexpMainMomentData.target_one h hi

end SubexponentialSAT.SubexpMainMomentStatics

end

end OAI.Algorithms
