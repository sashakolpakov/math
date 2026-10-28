import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.GradedExactness

/-! # Maps -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Maps.ProjectiveCech

noncomputable section

/-! The actual projective module Čech differential is natural in the module. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.GradedExactness.GradedModules

universe u v w t

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable {N : Type t} [AddCommGroup N] [Module R N] [Module (MvPolynomial σ R) N]
  [IsScalarTower R (MvPolynomial σ R) N]

theorem moduleChartRestriction_natural {s t : Finset σ} (h : s ⊆ t)
    (f : M →ₗ[MvPolynomial σ R] N) (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s) :
    Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R t) f (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h x) =
      Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R N h (Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) f x) := by
  obtain ⟨k, m, rfl⟩ := Presentations.Module.Fractions.GradedModules.moduleFractionMap_surj (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) x
  rw [Presentations.Module.ChartCompatibility.ProjectiveCech.moduleChartRestriction_fraction, Localized.GradedExactness.GradedModules.awayModuleMap_fraction, Localized.GradedExactness.GradedModules.awayModuleMap_fraction,
    Presentations.Module.ChartCompatibility.ProjectiveCech.moduleChartRestriction_fraction, map_smul]

def moduleCechMap (f : M →ₗ[MvPolynomial σ R] N) :
    Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M →ₗ[R] Card.ProjectiveCech.ModuleCechFamily (σ := σ) R N where
  toFun x s := Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) f (x s)
  map_add' x y := by
    funext s
    exact map_add _ (x s) (y s)
  map_smul' r x := by
    funext s
    exact map_smul _ r (x s)

theorem moduleCechMap_differential (f : M →ₗ[MvPolynomial σ R] N)
    (x : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    moduleCechMap R f (Card.ProjectiveCech.moduleCechDifferential R M x) =
      Card.ProjectiveCech.moduleCechDifferential R N (moduleCechMap R f x) := by
  funext s
  change Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) f
    (∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M
      (Finset.erase_subset i s) (x (s.erase i))) = _
  simp only [map_sum, map_smul, moduleChartRestriction_natural]
  rfl

omit [LinearOrder σ] in
theorem moduleCechMap_card (f : M →ₗ[MvPolynomial σ R] N) (q : ℕ)
    (x : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (hx : Card.ProjectiveCech.ModuleCechCardSupported R M q x) :
    Card.ProjectiveCech.ModuleCechCardSupported R N q (moduleCechMap R f x) := by
  intro s hs
  change Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) f (x s) = 0
  rw [hx s hs, map_zero]

variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
variable (𝒩 : ℤ → Submodule R N)

omit [LinearOrder σ] in
theorem moduleCechMap_homogeneous (f : M →ₗ[MvPolynomial σ R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (d : ℤ)
    (x : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (hx : Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d x) :
    Card.ProjectiveCech.ModuleCechHomogeneous R N 𝒩 d (moduleCechMap R f x) := by
  intro s
  exact Localized.GradedExactness.GradedModules.awayModuleMap_homogeneous (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ 𝒩
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) f hf d (x s) (hx s)

omit [LinearOrder σ] in
theorem moduleCechMap_injective (f : M →ₗ[MvPolynomial σ R] N) (hf : Function.Injective f) :
    Function.Injective (moduleCechMap R f) := by
  intro x y h
  funext s
  exact IsLocalizedModule.map_injective (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s))
    (LocalizedModule.mkLinearMap (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s)) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s)) N) f hf (congrFun h s)

variable {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial σ R) P]
  [IsScalarTower R (MvPolynomial σ R) P]

omit [LinearOrder σ] in
theorem moduleCechMap_exact (f : M →ₗ[MvPolynomial σ R] N) (g : N →ₗ[MvPolynomial σ R] P)
    (hex : Function.Exact f g) : Function.Exact (moduleCechMap R f) (moduleCechMap R g) := by
  have he (s : Finset σ) : Function.Exact
      (Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) f)
      (Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) g) :=
    LocalizedModule.map_exact (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s)) f g hex
  intro y
  constructor
  · intro hy
    choose x hx using fun s => (he s (y s)).mp (congrFun hy s)
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    funext s
    exact (he s _).mpr ⟨x s, rfl⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Maps.ProjectiveCech
