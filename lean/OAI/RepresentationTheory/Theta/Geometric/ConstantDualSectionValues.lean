import OAI.RepresentationTheory.Theta.Geometric.Dual.OpenSectionValues

/-! # Constant Dual Section Values -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConstantDualSectionValues

noncomputable section

/-! Constant dual-number points evaluate regular sections by the
canonical inclusion of their original complex value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem dualSectionValue_constant {X : Scheme} (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (U : X.Opens)
    (hp : p (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U)
    (hdual : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ p) ⁻¹ᵁ U)
    (s : Γ(X, U)) :
    Dual.OpenSectionValues.dualSectionValue (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ p) U hdual s =
      TrivSqZeroExt.inl (Complex.SectionEvaluation.complexSectionValue p U hp s) := by
  have hp' : (⊤ : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase.Opens) ≤ p ⁻¹ᵁ U := by
    intro t _
    change p t ∈ U
    rwa [Subsingleton.elim t (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)]
  have H := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) (p.appLE U ⊤ hp' s)
  have hc := Scheme.Hom.appLE_comp_appLE
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) p U ⊤ ⊤ hp' (by simp)
  have hc' := congrArg (fun f : Γ(X, U) ⟶ Γ(Spec (.of (DualNumber ℂ)), ⊤) =>
    (Scheme.ΓSpecIso (.of (DualNumber ℂ))).hom (f s)) hc
  exact hc'.symm.trans H

end

end OAI.RepresentationTheory.Theta.Geometric.ConstantDualSectionValues
