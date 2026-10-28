import OAI.AlgebraicGeometry.Comparison.Betti.Cech.Hypercohomology
import OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedHolomorphicAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Hypercohomology

/-! # Cech Hypercohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CechHypercohomology

noncomputable section

/-! The original holomorphic Čech total computes the independently defined holomorphic hypercohomology on every proved acyclic finite cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.Cech.Hypercohomology

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def holomorphicCechHypercohomologyEquiv {ι : Type} [Finite ι]
    (U : ι → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hU : ⨆ i, U i = ⊤)
    (hK : ∀ r, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) U
      (EmbeddedHolomorphicAcyclicity.nativeHolomorphicFormAdditiveSheaf X r)) (n : ℕ) :
    ((AdditiveCechPullbackBicomplex.nativeAdditiveCechBicomplex (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) U
      (ReferenceFormCechTotal.analyticHolomorphicAdditivePresheafComplex X)).total (.up ℕ)).homology n ≃+
        Hypercohomology.analyticHolomorphicCohomology X n :=
  Cech.Hypercohomology.cechHypercohomologyEquiv (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) U
    (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X) hU hK n

omit [IsIntegral X.left] [Smooth X.hom] in
theorem embeddedAnalyticCoordinateCover_covers (n : ℕ)
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) :
    (⨆ i, Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) = ⊤ := by
  change (⨆ i, (Opens.map (Analytification.Base.analytificationMap X)).obj (f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) = ⊤
  exact (Opens.map_iSup (Analytification.Base.analytificationMap X)
    (fun i => f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)).symm.trans
      (congrArg (Opens.map (Analytification.Base.analytificationMap X)).obj (EmbeddedHolomorphicAcyclicity.embeddedProjectiveCoordinateCover_covers n X f))

def embeddedHolomorphicCechHypercohomologyEquiv (n : ℕ)
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsClosedImmersion f.left] (q : ℕ) :
    ((AdditiveCechPullbackBicomplex.nativeAdditiveCechBicomplex (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (fun i => Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i))
      (ReferenceFormCechTotal.analyticHolomorphicAdditivePresheafComplex X)).total (.up ℕ)).homology q ≃+
        Hypercohomology.analyticHolomorphicCohomology X q :=
  holomorphicCechHypercohomologyEquiv X _ (embeddedAnalyticCoordinateCover_covers X n f)
    (EmbeddedHolomorphicAcyclicity.embeddedHolomorphicFormsCechAcyclic n X f) q

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CechHypercohomology
