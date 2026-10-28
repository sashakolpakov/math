import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationScalarRestriction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square

/-! # Coefficient Module Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientModuleCharts.ProjectiveCech

noncomputable section

/-! Actual module charts agree when the polynomial coefficient algebra is enlarged compatibly. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationScalarRestriction.GradedModules

universe u v w t

variable {σ : Type u}
variable (R : Type v) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem inversionMonomial_coefficientMap (s : Finset σ) :
    algebraMap (MvPolynomial σ R) (MvPolynomial σ S) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) =
      LaurentMonomials.ProjectiveCech.inversionMonomial S s := by
  simp only [MvPolynomial.algebraMap_def, LaurentMonomials.ProjectiveCech.inversionMonomial, MvPolynomial.map_monomial, map_one]

variable (M : Type t) [AddCommGroup M] [Module R M] [Module S M]
  [Module (MvPolynomial σ R) M] [Module (MvPolynomial σ S) M]
  [IsScalarTower R S M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ S) M] [IsScalarTower S (MvPolynomial σ S) M]
  [IsScalarTower (MvPolynomial σ R) (MvPolynomial σ S) M]

def coefficientModuleChartEquiv (s : Finset σ) : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s ≃ₗ[R] Graded.ModuleRestriction.ProjectiveCech.ModuleChart S M s :=
  LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq (R := R) M (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (LaurentMonomials.ProjectiveCech.inversionMonomial S s)
    (inversionMonomial_coefficientMap R S s)

omit [IsScalarTower R S M] in
theorem coefficientModuleChartEquiv_fraction (s : Finset σ) (k : ℕ) (m : M) :
    coefficientModuleChartEquiv R S M s (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) k m) =
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := S) (LaurentMonomials.ProjectiveCech.inversionMonomial S s) k m :=
  LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq_fraction M _ _ _ k m

variable [LinearOrder σ]

omit [IsScalarTower R S M] in
theorem coefficientModuleChartEquiv_restriction {s t : Finset σ} (h : s ⊆ t)
    (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s) :
    coefficientModuleChartEquiv R S M t (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h x) =
      Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction S M h (coefficientModuleChartEquiv R S M s x) :=
  LocalizationScalarRestriction.GradedModules.awayModuleScalarEquivOfEq_restriction M
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (LaurentMonomials.ProjectiveCech.inversionMonomial R t) (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s))
    (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h).symm
    (LaurentMonomials.ProjectiveCech.inversionMonomial S s) (LaurentMonomials.ProjectiveCech.inversionMonomial S t) (LaurentMonomials.ProjectiveCech.inversionMonomial S (t \ s))
    (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff S h).symm
    (inversionMonomial_coefficientMap R S s) (inversionMonomial_coefficientMap R S t)
    (inversionMonomial_coefficientMap R S (t \ s)) x

omit [Module R M] [Module S M] [Module (MvPolynomial σ R) M] [Module (MvPolynomial σ S) M]
  [AddCommGroup M] [IsScalarTower R S M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ S) M] [IsScalarTower S (MvPolynomial σ S) M]
  [IsScalarTower (MvPolynomial σ R) (MvPolynomial σ S) M] in
theorem alternatingSign_algebraMap (s : Finset σ) (i : σ) :
    algebraMap R S (Cech.Signs.ProjectiveCech.alternatingSign R s i) = Cech.Signs.ProjectiveCech.alternatingSign S s i := by
  simp only [Cech.Signs.ProjectiveCech.alternatingSign, map_pow, map_neg, map_one]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientModuleCharts.ProjectiveCech
