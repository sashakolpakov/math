import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientSingularSheafNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InjectiveSingularSheafSections

/-! # Singular Sheaf Section Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularSheafSectionCoefficients

noncomputable section

/-! The original singular sheafification map commutes with coefficient
change on actual global sections. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {R : Type} [Ring R] {M N : ModuleCat.{0} R} (f : M ⟶ N) (X : TopCat.{0})

def coefficientSheafSectionsMap : AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularSheafGlobalSections M X ⟶ AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularSheafGlobalSections N X :=
  (((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R) ⋙
    (evaluation (Opens X)ᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ))).map
      (CoefficientSingularSheafNaturality.coefficientSingularSheafMap f X)

theorem coefficientSheafSectionsMap_unit (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f (TopCat.of (⊤ : Opens X))).f n ≫
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf N X n)).app (op ⊤) =
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).app (op ⊤) ≫
      (coefficientSheafSectionsMap f X).f n :=
  congrArg (fun u => u.app (op (⊤ : Opens X)))
    (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
      ((CoefficientSingularSheafNaturality.coefficientSingularPresheafMap f X).f n))

theorem singularCochainsToSheafSections_coefficient :
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X ≫ AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections N X =
      AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M X ≫ coefficientSheafSectionsMap f X := by
  apply HomologicalComplex.Hom.ext
  funext n
  have hp := congrArg (fun u => u.f n)
    (AlgebraicTopology.Cohomology.Singular.Functor.coefficientCochainMap_naturality f (Opens.inclusion' (⊤ : Opens X)))
  exact (CoefficientComparisonDiagrams.two_comparison_squares _ _ _ _ _ _ _ hp
    (coefficientSheafSectionsMap_unit f X n).symm).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularSheafSectionCoefficients
