import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieTransport

/-! # Action Data Lie Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActionDataLieTransport.Construction

noncomputable section

/-! Lie-rank transport through an actual polarized-action data isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E k : Type} [Field E] [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable {A B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N (Spec (.of k))}

theorem polarizedActionIso_hasLieRank (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso A B)
    (τ : NumberField.RingOfIntegers E →+* k) (r : ℕ)
    (hr : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A.polarized.abelian A.action τ r) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank B.polarized.abelian B.action τ r :=
  AbelianModuli.ReferenceFamily.LieTransport.hasLieRank_transport A.action B.action e.polarized.abelian e.action τ r hr

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActionDataLieTransport.Construction
