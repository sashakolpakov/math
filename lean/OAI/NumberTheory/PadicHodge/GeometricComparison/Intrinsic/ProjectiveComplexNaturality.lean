import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ProjectiveComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Betti

/-! # Projective Complex Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ProjectiveComplexNaturality.ProjectiveComplexComparison

noncomputable section

/-! Naturality of the actual projective comparison uses the proved
naturality of the original smooth comparison map and the original form
and Betti universe coordinates. No BettiComparison input is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem lowerMap_naturality
    {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth X.hom] [IsProper X.hom]
    [Smooth Y.hom] [IsProper Y.hom] (f : X ⟶ Y) (n : ℕ) :
    (AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n).comp (AlgebraicGeometry.Comparison.Betti.OpenForms.algebraicDeRhamPullback f n).hom =
      (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom.comp
        (AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap Y n) := by
  unfold AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap
  exact Betti.ComplexComparison.lower_square (AlgebraicGeometry.Comparison.Betti.OpenForms.algebraicDeRhamPullback f n).hom
    (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n).hom (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap Y n).hom
    (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.bettiPullback f n).hom
    (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.bettiDownEquiv Y n).toLinearMap (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n).toLinearMap
    (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom
    (Betti.ComplexComparison.module_hom_square _ _ _ _ (AlgebraicGeometry.Comparison.Betti.Smooth.Naturality.smoothDeRhamBettiMap_naturality f n))
    (Betti.ComplexComparison.ulift_naturality _)

theorem nativeEquiv_naturality
    {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth X.hom] [IsProper X.hom]
    [Smooth Y.hom] [IsProper Y.hom]
    (PX : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (PY : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation Y.left Y.hom)
    (f : X ⟶ Y) (n : ℕ) :
    (ProjectiveComplex.ProjectiveComplexComparison.nativeEquiv X PX n).toLinearMap.comp (DeRham.Int.pullback f n) =
      (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom.comp (ProjectiveComplex.ProjectiveComplexComparison.nativeEquiv Y PY n).toLinearMap :=
  Betti.ComplexComparison.cancel_comparison_square
    (SheafFormsAdapter.FormsAdapter.cohomologyEquiv Y n) (SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n)
    (ProjectiveComplex.ProjectiveComplexComparison.nativeEquiv Y PY n).toLinearMap (ProjectiveComplex.ProjectiveComplexComparison.nativeEquiv X PX n).toLinearMap
    (AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap Y n) (AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n)
    (AlgebraicGeometry.Comparison.Betti.OpenForms.algebraicDeRhamPullback f n).hom (DeRham.Int.pullback f n)
    (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom
    (ProjectiveComplex.ProjectiveComplexComparison.nativeEquiv_comp_forms Y PY n) (ProjectiveComplex.ProjectiveComplexComparison.nativeEquiv_comp_forms X PX n)
    (LinearMap.ext (fun x => (DeRham.AdapterNaturality.FormsAdapter.cohomologyEquiv_pullback f n x).symm))
    (lowerMap_naturality f n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ProjectiveComplexNaturality.ProjectiveComplexComparison
