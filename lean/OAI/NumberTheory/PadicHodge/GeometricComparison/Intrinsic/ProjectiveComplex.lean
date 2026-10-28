import OAI.NumberTheory.PadicHodge.GeometricComparison.Betti
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.SmoothIsomorphism
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Components
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Naturality

/-! # Projective Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ProjectiveComplex.ProjectiveComplexComparison

noncomputable section

/-! The actual projective de Rham/Betti comparison and filtration
compatibility follow from the given projective presentation, without
assuming the full smooth-proper BettiComparison comparison proposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsProper X.hom]
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom)

def originalEquiv (n : ℕ) : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRham X n ≃ₗ[ℂ]
    AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n := by
  let := AlgebraicGeometry.Comparison.Betti.Projective.SmoothIsomorphism.projectivePresentation_smoothDeRhamBettiMap_isIso X P n
  exact Betti.ComplexComparison.equivOfBijective (AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n)
    ((AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n).bijective.comp
      ((asIso (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n)).toLinearEquiv.bijective))

theorem originalEquiv_toLinearMap (n : ℕ) :
    (originalEquiv X P n).toLinearMap = AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n :=
  Betti.ComplexComparison.equivOfBijective_toLinearMap _ _

def nativeEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ X n ≃ₗ[ℂ]
    AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n :=
  (SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n).symm.trans (originalEquiv X P n)

theorem nativeEquiv_comp_forms (n : ℕ) :
    (nativeEquiv X P n).toLinearMap.comp (SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n).toLinearMap =
      AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n :=
  (Betti.ComplexComparison.inverse_trans_comp (SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n) (originalEquiv X P n)).trans
    (originalEquiv_toLinearMap X P n)

theorem nativeEquiv_filtration (n : ℕ) (r : ℤ) :
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ X n r).map (nativeEquiv X P n).toLinearMap =
      AlgebraicGeometry.Comparison.Betti.Target.projectiveBettiHodgeFiltration (AlgebraicGeometry.Comparison.Betti.Target.projectivePresentation X P) n r := by
  have h₁ := congrArg (Submodule.map (nativeEquiv X P n).toLinearMap)
    (FilteredComplexAdapter.FormsAdapter.cohomologyEquiv_filtration X n r).symm
  have h₂ := (Submodule.map_comp (SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n).toLinearMap
    (nativeEquiv X P n).toLinearMap (FilteredComplexAdapter.FormsAdapter.filtration66 X n r)).symm
  have h₃ := congrArg (fun m => (FilteredComplexAdapter.FormsAdapter.filtration66 X n r).map m)
    (nativeEquiv_comp_forms X P n)
  exact h₁.trans (h₂.trans (h₃.trans
    (AlgebraicGeometry.Comparison.Betti.Projective.Components.projectivePresentation_hodgeFiltration_comparison X P n r)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ProjectiveComplex.ProjectiveComplexComparison
