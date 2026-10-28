import OAI.RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation

/-! # Top Section Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.TopSectionValues

noncomputable section

/-! The literal formula for evaluation of a global regular section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem complexSectionValue_top_formula {X : Scheme} (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (s : Γ(X, ⊤)) :
    RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue p ⊤ (by trivial) s = (Scheme.ΓSpecIso (.of ℂ)).hom (p.appTop s) := by
  have h : p.appLE ⊤ ⊤ (by intro x _; trivial) = p.appTop := p.appLE_eq_app
  exact congrArg (fun f : Γ(X, ⊤) ⟶ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) => (Scheme.ΓSpecIso (.of ℂ)).hom (f s)) h

theorem complexSectionValue_top_pullback {X Y : Scheme} (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X)
    (f : X ⟶ Y) (s : Γ(Y, ⊤)) :
    RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue (p ≫ f) ⊤ (by trivial) s =
      RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue p ⊤ (by trivial) (f.appTop s) := by
  rw [complexSectionValue_top_formula, complexSectionValue_top_formula, Scheme.Hom.comp_appTop]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.TopSectionValues
