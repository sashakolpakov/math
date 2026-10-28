import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockHeightIso

/-! # Action Data Height Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActionDataHeightTransport.Construction

noncomputable section

/-! Transport the full block-height witness through an actual
isomorphism of polarized, marked integral-action data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E k : Type} [Field E] [Field k] {g N q : ℕ} [Fact q.Prime] {δ : Fin g → ℕ}
variable {A B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N (Spec (.of k))}

theorem polarizedActionIso_hasBlockHeight (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso A B)
    (χ : NumberField.RingOfIntegers E →+* PadicInt q) (r : ℕ)
    (hr : PELModuli.CMPoints.BlocksProjectors.BlockHasHeight A.polarized.abelian A.action χ r) :
    PELModuli.CMPoints.BlocksProjectors.BlockHasHeight B.polarized.abelian B.action χ r :=
  PointsBlockHeightIso.Construction.l45BlockHasHeight_iso A.polarized.abelian B.polarized.abelian A.action B.action
    e.polarized.abelian e.action χ hr

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActionDataHeightTransport.Construction
