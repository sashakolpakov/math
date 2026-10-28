import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Maps

/-! # Retraction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Retraction.ProjectiveCech

noncomputable section

/-! Actual localized Čech maps preserve a retraction of polynomial modules. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable {N : Type t} [AddCommGroup N] [Module R N] [Module (MvPolynomial σ R) N]
  [IsScalarTower R (MvPolynomial σ R) N]

omit [LinearOrder σ] in
theorem moduleCechMap_retraction (i : M →ₗ[MvPolynomial σ R] N) (p : N →ₗ[MvPolynomial σ R] M)
    (hpi : ∀ m, p (i m) = m) (f : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    Maps.ProjectiveCech.moduleCechMap R p (Maps.ProjectiveCech.moduleCechMap R i f) = f := by
  funext s
  change Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) p
    (Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) i (f s)) = f s
  obtain ⟨k, m, hm⟩ := Presentations.Module.Fractions.GradedModules.moduleFractionMap_surj (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (f s)
  rw [← hm, Localized.GradedExactness.GradedModules.awayModuleMap_fraction, Localized.GradedExactness.GradedModules.awayModuleMap_fraction, hpi]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Retraction.ProjectiveCech
