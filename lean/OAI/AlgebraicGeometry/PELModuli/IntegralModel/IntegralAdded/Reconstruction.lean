import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId

/-! # Reconstruction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded

noncomputable section

/-! Reconstruct a two-level comparison from its prescribed-level
comparison and the actual equality of auxiliary markings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {T : Over (Spec (.of R))}

def PELId.IntegralAddedPELLevel.Iso.of_forgetAuxiliary
    {A B : PELId.IntegralAddedPELLevel P R iotaO L N T}
    (e : PEL.Iso.PolarizedActionIso A.forgetAuxiliary.data B.forgetAuxiliary.data)
    (h : A.auxiliary.data.polarized.level.transport e.polarized.abelian =
      B.auxiliary.data.polarized.level) : PELId.IntegralAddedPELLevel.Iso A B where
  auxiliary := {
    polarized := {
      abelian := e.polarized.abelian
      dual := e.polarized.dual
      abelianGroup := e.polarized.abelianGroup
      dualGroup := e.polarized.dualGroup
      polarization := e.polarized.polarization
      poincare := e.polarized.poincare
      level := fun V c => congrArg (fun β : B.auxiliary.data.polarized.abelian.FullLevel L =>
        (β.hom.app (.op V) c).val) h }
    action := e.action }
  prescribed := by
    apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
    exact e.polarized.level

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded
