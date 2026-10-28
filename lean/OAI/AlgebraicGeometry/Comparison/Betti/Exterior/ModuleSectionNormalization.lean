import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleForgetNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.AnalytifiedForm

/-! # Module Section Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleSectionNormalization

noncomputable section

/-! The actual algebraic symbol sections retain their original
sheafification classes under the module-forgetting isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

theorem exteriorFormsModuleSheafForgetIso_section (U : X.left.Opens) (n : ℕ)
    (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    (ModuleForget.exteriorFormsModuleSheafForgetIso X n).hom.hom.app (op U)
        (AnalytifiedForm.exteriorFormSheafSection X U n a) =
      (toSheafify (Opens.grothendieckTopology X.left) (Algebraic.Sheaves.formPresheaf X n)).app (op U) a := by
  have h := congrArg (fun k => k.app (op U)
      (Forms.exteriorFormsEquiv Γ(X.left, U) n a))
    (ModuleForgetNormalization.exteriorFormsModuleSheafForgetIso_unit X n)
  change (ModuleForget.exteriorFormsModuleSheafForgetIso X n).hom.hom.app (op U)
      (AnalytifiedForm.exteriorFormSheafSection X U n a) =
    (toSheafify (Opens.grothendieckTopology X.left) (Algebraic.Sheaves.formPresheaf X n)).app (op U)
      ((Forms.exteriorFormsEquiv Γ(X.left, U) n).symm
        (Forms.exteriorFormsEquiv Γ(X.left, U) n a)) at h
  exact h.trans (congrArg
    ((toSheafify (Opens.grothendieckTopology X.left) (Algebraic.Sheaves.formPresheaf X n)).app (op U))
    ((Forms.exteriorFormsEquiv Γ(X.left, U) n).symm_apply_apply a))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleSectionNormalization
