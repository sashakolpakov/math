import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DegreeMapExactness

/-! # Module Isomorphism -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ModuleIsomorphism.ProjectiveCech

noncomputable section

/-! Graded module isomorphisms preserve and reflect actual projective Čech exactness. -/

open _root_.MvPolynomial DirectSum

universe u v w t

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable {N : Type t} [AddCommGroup N] [Module R N] [Module (MvPolynomial σ R) N]
  [IsScalarTower R (MvPolynomial σ R) N]
variable (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)
variable [Decomposition ℳ] [Decomposition 𝒩]
variable [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩]

theorem moduleCechExactAt_iff_of_module_bijective (f : M →ₗ[MvPolynomial σ R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hbij : Function.Bijective f) (d : ℤ) (q : ℕ) :
    DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q ↔ DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R N 𝒩 d q := by
  apply DegreeMapExactness.ProjectiveCech.moduleCechExactAt_iff_of_degreeMap_bijective R ℳ 𝒩 f hf d
  intro s
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact IsLocalizedModule.map_injective (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s))
      (LocalizedModule.mkLinearMap (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s)) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s)) N) f hbij.1
      (congrArg Subtype.val hxy)
  · exact Localized.GradedExactness.GradedModules.localizedDegreeMap_surjective (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ 𝒩
      (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) f hf hbij.2 d

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ModuleIsomorphism.ProjectiveCech
