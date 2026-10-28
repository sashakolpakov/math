import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SmoothSheafCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.QuasiIso

/-! # Smooth Presheaf Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SmoothPresheafCech

noncomputable section

/-! The actual algebraic sheaf-to-smooth map remains a quasi-isomorphism
in the native complex-linear Čech coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]

theorem map_quasiIso (n : ℕ)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))) [IsClosedImmersion f.left] :
    QuasiIso (CechCoefficient.Naturality.Total.totalMap
      (FormalCoproduct.mk (Fin (n + 2))
        (fun i => f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i)).cech
      (AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicSheafToSmoothPresheafMap X)) := by
  apply Cech.QuasiIso.moduleCoefficients_of_forget
  let L := (AlgebraicGeometry.Comparison.Betti.Cech.ForgetModules.modulePresheafForget.mapHomologicalComplex (.up ℕ)).obj
    (AlgebraicGeometry.Comparison.Betti.Complex.SheafCechBicomplex.complexSheafPresheafComplex (TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
  exact Cech.QuasiIso.additiveCoefficients_of_pullback
    (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X)
    (fun i => f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i) (L := L)
    (CechCoefficient.Naturality.Total.mappedComplexMap
      (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})
      (AlgebraicGeometry.Comparison.Betti.ConcreteCech.algebraicSheafToSmoothPresheafMap X))
    (SmoothSheafCech.embedded_map_quasiIso X n f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SmoothPresheafCech
