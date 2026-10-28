import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationSectionComplexIso

/-! # Affine Section Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineSectionComplex.AffineCoordinates

noncomputable section

/-! Global sections of the native affine de Rham sheaf complex identify canonically with the native presheaf sections, including every differential. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]

abbrev affineSheafSections : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) ⥤ ModuleCat R :=
  sheafToPresheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (ModuleCat R) ⋙
    (CategoryTheory.evaluation _ _).obj (op ⊤)

instance affineSheafSections_additive : (affineSheafSections R A).Additive where
  map_add := by intros; rfl

theorem nativeComplex_unit_top_isIso (n : ℕ) :
    IsIso ((toSheafify (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)).X n)).app (op ⊤)) := by
  change IsIso ((toSheafify (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n)).app (op ⊤))
  exact AffineFormsUnit.AffineCoordinates.nativeForms_unit_top_isIso R A n

def nativeSectionComplexIso :
    (((CategoryTheory.evaluation _ (ModuleCat R)).obj (op (⊤ : (Spec (CommRingCat.of A)).Opens))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)) ≅
    ((affineSheafSections R A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)) :=
  SheafificationSectionComplexIso.SheafificationSectionComplex.complexIso (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
    (ComplexShape.up ℕ) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)) (op ⊤)
    (nativeComplex_unit_top_isIso R A)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineSectionComplex.AffineCoordinates
