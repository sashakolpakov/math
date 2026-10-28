import OAI.RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation

/-! # Section Value Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.SectionValueTransport

noncomputable section

/-! Global dual-number section values transport along an actual
commuting triangle of schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem dualSectionValue_transport {X Y : Scheme}
    (p : Spec (.of (DualNumber ℂ)) ⟶ X) (f : X ⟶ Y)
    (q : Spec (.of (DualNumber ℂ)) ⟶ Y) (h : p ≫ f = q) (s : Γ(Y, ⊤)) :
    RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue p (f.appTop s) = RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue q s :=
  (RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue_pullback p f s).symm.trans
    (congrArg (fun t : Spec (.of (DualNumber ℂ)) ⟶ Y => RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue t s) h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.SectionValueTransport
