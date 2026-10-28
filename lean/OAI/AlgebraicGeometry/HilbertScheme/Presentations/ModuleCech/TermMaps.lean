import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.ExactSequences

/-! # Term Maps -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.TermMaps.ProjectiveCech

noncomputable section

/-! Maps and exact sequences on the actual homogeneous Čech terms. -/

open _root_.MvPolynomial DirectSum

universe u v w t z

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable {N : Type t} [AddCommGroup N] [Module R N] [Module (MvPolynomial σ R) N]
  [IsScalarTower R (MvPolynomial σ R) N]
variable (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

def moduleCechTermMap (f : M →ₗ[MvPolynomial σ R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (d : ℤ) (q : ℕ) :
    Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d q →ₗ[R] Terms.ProjectiveCech.moduleCechTerm (σ := σ) R N 𝒩 d q :=
  ((Maps.ProjectiveCech.moduleCechMap R f).comp (Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d q).subtype).codRestrict _
    (fun x => ⟨Maps.ProjectiveCech.moduleCechMap_homogeneous R ℳ 𝒩 f hf d x.val x.property.1,
      Maps.ProjectiveCech.moduleCechMap_card R f q x.val x.property.2⟩)

omit [LinearOrder σ] in
theorem moduleCechTermMap_injective (f : M →ₗ[MvPolynomial σ R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hfinj : Function.Injective f) (d : ℤ) (q : ℕ) :
    Function.Injective (moduleCechTermMap R ℳ 𝒩 f hf d q) := by
  intro x y hxy
  apply Subtype.ext
  exact Maps.ProjectiveCech.moduleCechMap_injective R f hfinj (congrArg Subtype.val hxy)

variable [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩]

theorem moduleCechTermMap_differential (f : M →ₗ[MvPolynomial σ R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (d : ℤ) (q : ℕ)
    (x : Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d q) :
    moduleCechTermMap R ℳ 𝒩 f hf d (q + 1) (Terms.ProjectiveCech.moduleCechTermDifferential R M ℳ d q x) =
      Terms.ProjectiveCech.moduleCechTermDifferential R N 𝒩 d q (moduleCechTermMap R ℳ 𝒩 f hf d q x) := by
  apply Subtype.ext
  exact Maps.ProjectiveCech.moduleCechMap_differential R f x.val

variable [Decomposition ℳ] [Decomposition 𝒩]

omit [LinearOrder σ] in
theorem moduleCechTermMap_surjective (f : M →ₗ[MvPolynomial σ R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hfsurj : Function.Surjective f) (d : ℤ) (q : ℕ) :
    Function.Surjective (moduleCechTermMap R ℳ 𝒩 f hf d q) := by
  intro y
  obtain ⟨x, hx, hxc, hxy⟩ := ExactSequences.ProjectiveCech.moduleCechMap_lift R ℳ 𝒩 f hf hfsurj d q y.val y.property.1 y.property.2
  exact ⟨⟨x, hx, hxc⟩, Subtype.ext hxy⟩

variable {P : Type z} [AddCommGroup P] [Module R P] [Module (MvPolynomial σ R) P]
  [IsScalarTower R (MvPolynomial σ R) P]
variable (ℙ : ℤ → Submodule R P)

omit [LinearOrder σ] in
theorem moduleCechTermMap_exact (f : M →ₗ[MvPolynomial σ R] N) (g : N →ₗ[MvPolynomial σ R] P)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hg : ∀ d m, m ∈ 𝒩 d → g m ∈ ℙ d)
    (hex : Function.Exact f g) (d : ℤ) (q : ℕ) :
    Function.Exact (moduleCechTermMap R ℳ 𝒩 f hf d q) (moduleCechTermMap R 𝒩 ℙ g hg d q) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, hxc, hxy⟩ := ExactSequences.ProjectiveCech.moduleCechMap_kernel_lift R ℳ 𝒩 ℙ f g hf hg hex d q
      y.val y.property.1 y.property.2 (congrArg Subtype.val hy)
    exact ⟨⟨x, hx, hxc⟩, Subtype.ext hxy⟩
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    exact (Maps.ProjectiveCech.moduleCechMap_exact R f g hex _).mpr ⟨x.val, rfl⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.TermMaps.ProjectiveCech
