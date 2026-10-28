import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FormRestriction
import OAI.AlgebraicGeometry.Comparison.Betti.DisjointDerivedHom

/-! # Open Cohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OpenCohomology

noncomputable section

/-! Identification of restricted algebraic hypercohomology using the original open pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsOpenImmersion f.left]

def openAlgebraicComplexIso :
    ((Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Sheaves.algebraicDeRhamSheafComplexInt Y) ≅ Sheaves.algebraicDeRhamSheafComplexInt X := by
  have := FormRestriction.deRhamSheafPullbackInt_isIso_of_openImmersion f
  exact asIso (OpenForms.deRhamSheafPullbackInt f)

def openAlgebraicHypercohomologyEquiv (n : ℕ) :
    DisjointDerivedHom.complexHypercohomology (TopCat.of X.left)
        (((Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (Sheaves.algebraicDeRhamSheafComplexInt Y)) (n : ℤ) ≃ₗ[ℂ] Sheaves.algebraicDeRham X n :=
  Linear.homCongr ℂ (Iso.refl _)
    ((shiftFunctor (DerivedCategory (Sheaves.ComplexSheaves X)) (n : ℤ)).mapIso
      (DerivedCategory.Q.mapIso (openAlgebraicComplexIso f)))

theorem openAlgebraicHypercohomologyEquiv_apply (n : ℕ)
    (a : DisjointDerivedHom.complexHypercohomology (TopCat.of X.left)
      (((Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Sheaves.algebraicDeRhamSheafComplexInt Y)) (n : ℤ)) :
    openAlgebraicHypercohomologyEquiv f n a =
      a ≫ (DerivedCategory.Q.map (OpenForms.deRhamSheafPullbackInt f))⟦(n : ℤ)⟧' := by
  change (𝟙 _ ≫ a) ≫ _ = _
  rw [Category.id_comp]
  rfl

theorem openAlgebraicHypercohomologyEquiv_pullback (n : ℕ) (a : Sheaves.algebraicDeRham Y n) :
    openAlgebraicHypercohomologyEquiv f n
      (DisjointDerivedHom.inverseImageHypercohomologyMap f.left.base
        (Sheaves.algebraicDeRhamSheafComplexInt Y) (n : ℤ) a) = OpenForms.algebraicDeRhamPullback f n a := by
  erw [openAlgebraicHypercohomologyEquiv_apply]
  simp only [DisjointDerivedHom.inverseImageHypercohomologyMap, LinearMap.coe_mk,
    AddHom.coe_mk, ShiftedHom.map, Category.assoc]
  change ((OpenForms.derivedInverseImageConstantIso f).inv ≫
    (Sheaves.derivedInverseImage f).map a ≫
    ((Sheaves.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
      (DerivedCategory.Q.obj (Sheaves.algebraicDeRhamSheafComplexInt Y)) ≫
    ((Sheaves.inverseImage f).mapDerivedCategoryFactors.hom.app
      (Sheaves.algebraicDeRhamSheafComplexInt Y))⟦(n : ℤ)⟧') ≫
    (DerivedCategory.Q.map (OpenForms.deRhamSheafPullbackInt f))⟦(n : ℤ)⟧' =
      (OpenForms.derivedInverseImageConstantIso f).inv ≫ (Sheaves.derivedInverseImage f).map a ≫
        ((Sheaves.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
          (DerivedCategory.Q.obj (Sheaves.algebraicDeRhamSheafComplexInt Y)) ≫
        (OpenForms.derivedDeRhamPullback f)⟦(n : ℤ)⟧'
  simp only [OpenForms.derivedDeRhamPullback, Category.assoc]
  exact congrArg (fun t => (OpenForms.derivedInverseImageConstantIso f).inv ≫
    (Sheaves.derivedInverseImage f).map a ≫
    ((Sheaves.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
      (DerivedCategory.Q.obj (Sheaves.algebraicDeRhamSheafComplexInt Y)) ≫ t)
    ((shiftFunctor (DerivedCategory (Sheaves.ComplexSheaves X)) (n : ℤ)).map_comp
      ((Sheaves.inverseImage f).mapDerivedCategoryFactors.hom.app (Sheaves.algebraicDeRhamSheafComplexInt Y))
      (DerivedCategory.Q.map (OpenForms.deRhamSheafPullbackInt f))).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OpenCohomology
