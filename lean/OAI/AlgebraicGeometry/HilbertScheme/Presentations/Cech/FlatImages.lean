import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.FlatAugmentation

/-! # Flat Images -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.FlatImages.ProjectiveCech

noncomputable section

/-! Higher exactness and flat projective charts give flat images in every positive homogeneous Čech degree. -/

open _root_.MvPolynomial

universe u v

variable {σ : Type v} [Fintype σ] [LinearOrder σ]
variable (R : Type u) [CommRing R]
variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

theorem moduleCech_positive_image_flat (d : ℤ)
    (hflat : ∀ s : Finset σ, s.Nonempty → Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d))
    (hex : ∀ q : ℕ, DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d (q + 2)) (q : ℕ) :
    Module.Flat R (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d (q + 1)).range := by
  let V : ℕ → Type (max u v) := fun k => ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d (q + 2 + k)
  let D : ∀ k, V k →ₗ[R] V (k + 1) := fun k => ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d (q + 2 + k)
  have hker : Module.Flat R (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d (q + 2)).ker := by
    apply Presentations.Flat.BoundedComplex.flat_kernel_of_bounded_exact R (Fintype.card σ) V D
    · intro k
      apply FlatAugmentation.ProjectiveCech.moduleCechTermDifferential_exact R M ℳ d (q + 2 + k)
      have hi : q + k + 1 + 2 = q + 2 + k + 1 := by omega
      simpa only [hi] using hex (q + k + 1)
    · exact ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_zero R M ℳ d (q + 2 + Fintype.card σ) (by omega)
    · intro k _
      exact ModuleCech.Terms.ProjectiveCech.moduleCechTerm_flat R M ℳ d (q + 2 + k) (by omega) hflat
  let : Module.Flat R (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d (q + 2)).ker := hker
  have he := (FlatAugmentation.ProjectiveCech.moduleCechTermDifferential_exact R M ℳ d (q + 1) (hex q)).linearMap_ker_eq.symm
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _ he)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.FlatImages.ProjectiveCech
