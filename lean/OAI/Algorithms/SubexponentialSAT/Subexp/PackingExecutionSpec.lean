import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrontendData
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingAddressSemantics

namespace OAI.Algorithms

/-! Input representation for the actual packing controller. No block, selected
vertex, leftover list, address, or output table is supplied by this structure. -/

namespace SubexponentialSAT.Subexp.PackingExecution

open ConstructivePacking

structure Spec (U : Type*) [DecidableEq U] where
  params : PackingFrontend.Params
  types : FiniteEnumeration U
  label : Fin params.D → U
  encodeType : U → List Bool
  encodeType_injective : Function.Injective encodeType
  rows_width : ∀ row ∈ params.rows, row.length = params.width.length
  rows_count : params.rows.length = params.scopes.length + (params.Δ + 1) * params.D
  degree_bound : ∀ v : Fin params.D, IncidencePlanSpec.degree params.scopes v.val ≤ params.Δ
  label_records : PackingVertexLabels.labelRecords params.rows params.planList 0 =
    BucketProgram.vertexRecords (List.finRange params.D) label encodeType
      (fun v => List.replicate v.val true)
  type_records : params.typeRows = types.values.map encodeType

namespace Spec

variable {U : Type*} [DecidableEq U]

/-- The packing algorithm is the existing executable bucket/minimum/index
construction applied only to the represented input labels and type list. -/
def packing (s : Spec U) : PackingData (Fin s.params.D) U :=
  ⟨⟨List.finRange s.params.D, List.nodup_finRange _, List.mem_finRange⟩, s.types, s.label⟩

def encodeVertex (s : Spec U) (v : Fin s.params.D) : List Bool := List.replicate v.val true

def metadata (s : Spec U) : List Bool :=
  SelectorProgram.rawRecords (PackingMetadata.records s.packing s.encodeVertex s.encodeType)

def addresses (s : Spec U) : List Bool :=
  SelectorProgram.rawRecords (PackingAddressSemantics.addressRows
    ((PackingReorder.storageVertices s.packing).map s.encodeVertex) 0).reverse

def storage (s : Spec U) : List Bool :=
  ProgramEncoding.encodeRecords ((PackingReorder.storageVertices s.packing).map s.encodeVertex)

def inverse (s : Spec U) : List Bool :=
  ProgramEncoding.encodeRecords ((PackingReorder.readPlan s.packing).map PackingMetadata.unary)

def outputState (s : Spec U) (regs : Fin 16 → Bool) : PackingProgramSupport.Data :=
  PackingProgram.outputState s.params.input
    (List.replicate s.packing.blockCount true) (List.replicate s.packing.leftovers.length true)
    s.metadata s.addresses s.storage s.inverse regs

@[simp] theorem packing_vertices (s : Spec U) : s.packing.vertices.values = List.finRange s.params.D := rfl
@[simp] theorem packing_label (s : Spec U) : s.packing.label = s.label := rfl
@[simp] theorem packing_types (s : Spec U) : s.packing.types = s.types := rfl

theorem encodeVertex_injective (s : Spec U) : Function.Injective s.encodeVertex := by
  intro v w h
  apply Fin.ext
  have hl := congrArg List.length h
  simpa [encodeVertex] using hl

end Spec
end SubexponentialSAT.Subexp.PackingExecution

end OAI.Algorithms
