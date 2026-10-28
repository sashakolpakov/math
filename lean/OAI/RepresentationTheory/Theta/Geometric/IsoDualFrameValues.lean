import OAI.RepresentationTheory.Theta.Geometric.Dual.OpenSectionValues
import OAI.RepresentationTheory.Theta.Geometric.ModuleIsoFrameUnits

/-! # Iso Dual Frame Values -/

namespace OAI.RepresentationTheory.Theta.Geometric.IsoDualFrameValues

noncomputable section

/-! The genuine coefficients of a native line-bundle isomorphism satisfy
their change-of-frame equation at every actual dual-number point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem moduleIsoFrameUnit_dualValue_transition {X : Scheme} {M N : X.Modules}
    (f : M ≅ N) (U : X.Opens)
    (e e' : M.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (g g' : N.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (p : Spec (.of (DualNumber ℂ)) ⟶ X)
    (hp : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤ p ⁻¹ᵁ U) :
    Dual.OpenSectionValues.dualSectionValue p U hp (ModuleIsoFrameUnits.moduleIsoFrameUnit f U e g : Γ(X, U)) *
        Dual.OpenSectionValues.dualSectionValue p U hp (IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e e' : Γ(X, U)) =
      Dual.OpenSectionValues.dualSectionValue p U hp (IntrinsicFrame.TransitionUnits.frameTransitionUnit N U g g' : Γ(X, U)) *
        Dual.OpenSectionValues.dualSectionValue p U hp (ModuleIsoFrameUnits.moduleIsoFrameUnit f U e' g' : Γ(X, U)) := by
  have H := congrArg (fun u : Γ(X, U)ˣ => Dual.OpenSectionValues.dualSectionValue p U hp (u : Γ(X, U)))
    (ModuleIsoFrameUnits.moduleIsoFrameUnit_transition f U e e' g g')
  simpa only [Units.val_mul, map_mul] using H

end

end OAI.RepresentationTheory.Theta.Geometric.IsoDualFrameValues
