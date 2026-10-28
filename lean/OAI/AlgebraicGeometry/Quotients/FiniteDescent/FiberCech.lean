import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RingEquiv
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberScalar

/-! # Fiber Cech -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberCech

noncomputable section

/-! Detection computed using the geometric fiber's spectral sections is
also detection over the local residue field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.FiberCechDetection

theorem from_spectrum (S : Scheme.{u}) (x : S)
    {C T₁ T₂ : ShortComplex (ModuleCat.{u} Γ(S, ⊤))} (r₁ : C ⟶ T₁) (r₂ : C ⟶ T₂)
    (hd : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapShortComplex.map r₁)
      ((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapShortComplex.map r₂)) :
    CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map r₁)
      ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map r₂) := by
  let e := (Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv
  have h := RingEquiv.Construction.RingEquivCechDetection.composite e (S.fromSpecResidueField x).appTop.hom r₁ r₂ hd
  have he : e.toRingHom.comp (S.fromSpecResidueField x).appTop.hom = (S.Γevaluation x).hom :=
    congrArg (fun a : Γ(S, ⊤) ⟶ S.residueField x => a.hom) (FiberScalar.Construction.FiberScalarMaps.fromResidue_appTop S x)
  rw [he] at h
  exact h

end Construction.FiberCechDetection

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberCech
