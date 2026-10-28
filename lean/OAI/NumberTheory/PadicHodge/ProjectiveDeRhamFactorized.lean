import OAI.AlgebraicGeometry.Comparison.Betti.Projective.SmoothIsomorphism
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Components
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Naturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.AdapterNaturality

/-! # Projective De Rham Factorized -/

namespace OAI.NumberTheory.PadicHodge.ProjectiveDeRhamFactorized.FrobeniusSlope

noncomputable section

/-! Restricted comparison on the actual smooth projective varieties needed here.
No full BettiComparison or GeometricComparison comparison proposition is an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Lower an isomorphism in a module category without expanding its inverse. -/
theorem lowered_iso_toLinearMap {U V : ModuleCat.{1} ℂ} {W : Type*}
    [AddCommGroup W] [Module ℂ W]
    (f : U ⟶ V) [IsIso f] (e : V ≃ₗ[ℂ] W) :
    ((asIso f).toLinearEquiv.trans e).toLinearMap = e.toLinearMap.comp f.hom := by
  apply LinearMap.ext
  intro x
  rfl

/-- Cancel an adapter before any geometric cohomology objects are instantiated. -/
theorem adapter_cancel {U V W : Type*} [AddCommGroup U] [AddCommGroup V]
    [AddCommGroup W] [Module ℂ U] [Module ℂ V] [Module ℂ W]
    (e : U ≃ₗ[ℂ] V) (f : U ≃ₗ[ℂ] W) :
    (e.symm.trans f).toLinearMap.comp e.toLinearMap = f.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact congrArg f (e.symm_apply_apply x)

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsProper X.hom]
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (n : ℕ)

def algebraicBettiEquiv : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRham X n ≃ₗ[ℂ]
    AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n := by
  let : IsIso (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n) :=
    AlgebraicGeometry.Comparison.Betti.Projective.SmoothIsomorphism.projectivePresentation_smoothDeRhamBettiMap_isIso X P n
  exact (asIso (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n)).toLinearEquiv.trans
    (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n)

theorem algebraicBettiEquiv_toLinearMap :
    (algebraicBettiEquiv X P n).toLinearMap = AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n := by
  let : IsIso (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n) :=
    AlgebraicGeometry.Comparison.Betti.Projective.SmoothIsomorphism.projectivePresentation_smoothDeRhamBettiMap_isIso X P n
  exact lowered_iso_toLinearMap (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n)
    (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n)

/-- The original native de Rham object, not a redefinition through Betti. -/
def nativeBettiEquiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ X n ≃ₗ[ℂ]
    AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n :=
  (GeometricComparison.SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n).symm.trans (algebraicBettiEquiv X P n)

theorem nativeBettiEquiv_comp_forms :
    (nativeBettiEquiv X P n).toLinearMap.comp (GeometricComparison.SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n).toLinearMap =
      AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n := by
  exact (adapter_cancel (GeometricComparison.SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n) (algebraicBettiEquiv X P n)).trans
    (algebraicBettiEquiv_toLinearMap X P n)

/-- Equality of the independently constructed native and Betti filtrations. -/
theorem nativeBettiEquiv_filtration (r : ℤ) :
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ X n r).map (nativeBettiEquiv X P n).toLinearMap =
      AlgebraicGeometry.Comparison.Betti.Target.projectiveBettiHodgeFiltration (AlgebraicGeometry.Comparison.Betti.Target.projectivePresentation X P) n r := by
  have h₁ := congrArg (Submodule.map (nativeBettiEquiv X P n).toLinearMap)
    (GeometricComparison.FilteredComplexAdapter.FormsAdapter.cohomologyEquiv_filtration X n r).symm
  have h₂ := (Submodule.map_comp (GeometricComparison.SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n).toLinearMap
    (nativeBettiEquiv X P n).toLinearMap (GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66 X n r)).symm
  have h₃ := congrArg (fun m => (GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66 X n r).map m)
    (nativeBettiEquiv_comp_forms X P n)
  exact h₁.trans (h₂.trans (h₃.trans
    (AlgebraicGeometry.Comparison.Betti.Projective.Components.projectivePresentation_hodgeFiltration_comparison X P n r)))

end

end OAI.NumberTheory.PadicHodge.ProjectiveDeRhamFactorized.FrobeniusSlope
