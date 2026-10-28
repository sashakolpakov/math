import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputAddressed

namespace OAI.Algorithms

/-! The saved runtime plan stream uses absolute word addresses: the factor
component is ambient+factor. This constructor matches those bytes while
preserving the incidence order, owner fibers, packing, and head relation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open PackingCallerProgram LeafParametersProgram

variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
variable (a : Word (LeafProgram.Query.packingProblem q k hg).r
  (LeafProgram.Query.packingProblem q k hg).Q)
variable (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
  (LeafProgram.Query.packingProblem q k hg).Q))
variable (t : Fin (LeafProgram.Query.packingProblem q k hg).Q)

def queryInputsAddressed : Inputs :=
  { queryInputs q k hg a tail t with
    plans := PackingIncidenceInput.addressedEntries q.scopeRows
      (LeafProgram.Query.packingProblem q k hg).n q.forward
    plans_length := by
      rw [PackingIncidenceInput.addressedEntries_length]
      rfl
    fiber_degree := by
      intro v hv
      rw [PackingIncidenceInput.addressedEntries_fibers]
      exact ProducedQueryRank.query_fiber_length_le q k hg ⟨v,hv⟩ }

@[simp] theorem queryInputsAddressed_plans :
    (queryInputsAddressed q k hg a tail t).plans=
      PackingIncidenceInput.addressedEntries q.scopeRows
        (LeafProgram.Query.packingProblem q k hg).n q.forward := rfl

@[simp] theorem queryInputsAddressed_offset :
    (queryInputsAddressed q k hg a tail t).offset=ProducedQueryRank.queryHeight q k := rfl

@[simp] theorem queryInputsAddressed_packing :
    (queryInputsAddressed q k hg a tail t).packing=(queryInputs q k hg a tail t).packing := rfl

@[simp] theorem queryInputsAddressed_rows :
    (queryInputsAddressed q k hg a tail t).rows=(queryInputs q k hg a tail t).rows := rfl

@[simp] theorem queryInputsAddressed_columnLength :
    (queryInputsAddressed q k hg a tail t).columnLength=
      (queryInputs q k hg a tail t).columnLength := rfl

theorem queryInputsAddressed_fibers (v start : ℕ) :
    LayoutOwnerFiberProgram.fiberIndices v start (queryInputsAddressed q k hg a tail t).plans=
      LayoutOwnerFiberProgram.fiberIndices v start (queryInputs q k hg a tail t).plans :=
  PackingIncidenceInput.addressedEntries_fibers _ _ _ _ _

/-- The exact signed owner-fiber matrix relation is unchanged. In particular
the existing rank certificate applies to the corrected physical stream. -/
theorem queryInputsAddressed_relation :
    (queryInputsAddressed q k hg a tail t).relation=(queryInputs q k hg a tail t).relation := by
  funext j v pair
  unfold Inputs.relation BucketProgram.ProducedRank.FiberRel
  rw [queryInputsAddressed_fibers]
  rfl

/-- This is the literal byte string saved at parked master738 and loaded
into source136. It is not the raw unshifted incidence-pair serialization. -/
theorem queryInputsAddressed_stream :
    LayoutOwnerFiberProgram.stream (queryInputsAddressed q k hg a tail t).plans=
      PackingCallerProgram.planBits q.scopeRows
        (LeafProgram.Query.packingProblem q k hg).n q.forward :=
  PackingIncidenceInput.addressedEntries_stream _ _ _

theorem queryInputsAddressed_records_bytes :
    SubexponentialSAT.Encoding.encodeList id (queryInputsAddressed q k hg a tail t).records=
      PackingCallerProgram.planBits q.scopeRows
        (LeafProgram.Query.packingProblem q k hg).n q.forward :=
  (Inputs.records_bytes _).trans (queryInputsAddressed_stream q k hg a tail t)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
