import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleSectionNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ImageForget

/-! # Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.Normalization

noncomputable section

/-! The actual module comparison, after forgetting coefficient actions,
is exactly the preserved algebraic-to-holomorphic map of form sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem algebraicToHolomorphicSheafMap_section (U : X.left.Opens) (n : ℕ)
    (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    ((Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X).f n).hom.app (op U)
        ((toSheafify (Opens.grothendieckTopology X.left) (Algebraic.Sheaves.formPresheaf X n)).app (op U) a) =
      (Holomorphic.SheafSections.holomorphicSheafSectionIso (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
        (Open.AffineIsoEvaluation.analyticOpen X U) n).hom ((Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a) := by
  have h := congrArg (fun k => (k.f n).app (op U) a)
    (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap_normalization X)
  exact h

/-- The square compares the actual maps and the fixed form-sheaf adapters. -/
theorem exteriorToHolomorphicModuleSheafMap_forget (n : ℕ) :
    (Exterior.ModuleForget.exteriorFormsModuleSheafForgetIso X n).hom ≫
      (sheafCompose (Opens.grothendieckTopology X.left)
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).map
          ((Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X).f n) =
    (SheafOfModules.toSheaf.{0} X.left.ringCatSheaf).map
        (AnalytifiedForm.exteriorToHolomorphicModuleSheafMap X n) ≫
      (Holomorphic.ImageForget.zariskiHolomorphicModuleForgetIso X n).hom := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Opens.grothendieckTopology X.left) _ _
    ((sheafCompose (Opens.grothendieckTopology X.left)
      (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
        ((Algebraic.HolomorphicSheafMap.zariskiHolomorphicSheafComplex X).X n)).property
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  obtain ⟨a, rfl⟩ := (Exterior.Forms.exteriorFormsEquiv Γ(X.left, U.unop) n).surjective a
  change ((Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X).f n).hom.app U
      ((Exterior.ModuleForget.exteriorFormsModuleSheafForgetIso X n).hom.hom.app U
        (AnalytifiedForm.exteriorFormSheafSection X U.unop n a)) =
    (Holomorphic.ImageForget.zariskiHolomorphicModuleForgetIso X n).hom.hom.app U
      ((AnalytifiedForm.exteriorToHolomorphicModuleSheafMap X n).val.app U
        (AnalytifiedForm.exteriorFormSheafSection X U.unop n a))
  rw [Exterior.ModuleSectionNormalization.exteriorFormsModuleSheafForgetIso_section, AnalytifiedForm.exteriorFormSheafSection_comparison]
  exact algebraicToHolomorphicSheafMap_section X U.unop n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.Normalization
