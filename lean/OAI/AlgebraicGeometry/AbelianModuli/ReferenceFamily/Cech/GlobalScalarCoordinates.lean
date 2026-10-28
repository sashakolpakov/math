import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.GlobalCoefficientFormula
import OAI.AlgebraicGeometry.SheafCohomology.CechScalars
import OAI.AlgebraicGeometry.SheafCohomology.Cech.CochainExact

/-! # Global Scalar Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.GlobalScalarCoordinates

noncomputable section

/-! The scalar structure on global Cech module sections agrees with
the original native Cech action of global regular functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.TopCat.Sheaf

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

theorem cechGlobalModuleCoordinates_smul (n : ℕ) (r : Γ(X, ⊤)) (c : Γ(TermModules.cechTermModule X U n, ⊤)) :
    GlobalModuleCoordinates.cechGlobalModuleCoordinates X U n (r • c) =
      ((CategoryTheory.cechComplexFunctor U).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (SheafCohomology.AffineH.Projective.globalSmulHom (HilbertConstruction.Line.Bundles.structureModule X) r)).hom).f n
        (GlobalModuleCoordinates.cechGlobalModuleCoordinates X U n c) := by
  let F := TermModules.structureAbelianSheaf X
  let f : F ⟶ F := (SheafOfModules.toSheaf X.ringCatSheaf).map (SheafCohomology.AffineH.Projective.globalSmulHom (HilbertConstruction.Line.Bundles.structureModule X) r)
  apply (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U n).injective
  funext i
  have hn := SheafCohomology.Cech.CochainExact.TopCat.Sheaf.cechCochainFunctor_map_apply U f n (GlobalModuleCoordinates.cechGlobalModuleCoordinates X U n c) i
  change SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U n
    (((CategoryTheory.cechComplexFunctor U).map f.hom).f n (GlobalModuleCoordinates.cechGlobalModuleCoordinates X U n c)) i =
      f.hom.app (op (ExtensionCoordinates.cechIntersection U n i))
        (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U n (GlobalModuleCoordinates.cechGlobalModuleCoordinates X U n c) i) at hn
  erw [hn, GlobalCoefficientFormula.cechGlobalModuleCoordinates_coefficient, GlobalCoefficientFormula.cechGlobalModuleCoordinates_coefficient]
  erw [ExtensionCoordinates.cechCoefficient_smul]
  let T := ExtensionCoordinates.cechIntersection U n i
  change X.presheaf.map (eqToIso (congrArg op (top_inf_eq T))).hom
      (X.presheaf.map (homOfLE (show ⊤ ⊓ T ≤ ⊤ from inf_le_left)).op r * ExtensionCoordinates.cechCoefficient U n ⊤ c i) =
    X.presheaf.map (homOfLE (show T ≤ ⊤ from le_top)).op r *
      X.presheaf.map (eqToIso (congrArg op (top_inf_eq T))).hom (ExtensionCoordinates.cechCoefficient U n ⊤ c i)
  erw [map_mul]
  congr 1
  exact ConcreteCategory.congr_hom
    ((X.presheaf.map_comp _ _).symm.trans
      (congrArg X.presheaf.map (Subsingleton.elim _ _))) r

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.GlobalScalarCoordinates
