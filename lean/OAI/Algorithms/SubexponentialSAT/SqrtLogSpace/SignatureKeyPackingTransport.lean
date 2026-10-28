import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputPackingTransport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrixNatural

/-! Exact incidence-index transport for the canonical native source factory.
The ordinary full-label equality bridge is independent of this transport. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
variable {r Q n : ℕ}

/-- Changing the displayed incidence-list length preserves each natural
matrix address and transports only its typed owner index. -/
theorem literalNat_reindex {D E : ℕ} (h : D = E)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (A R : ℕ) (t : Fin Q) (j v : ℕ) :
    LayoutProducedMatrix.literalNat (PackingIncidenceInput.reindexPacking h P)
        (owner ∘ Fin.cast h.symm) A R t j v =
      LayoutProducedMatrix.literalNat P owner A R t j v := by
  cases h
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource
