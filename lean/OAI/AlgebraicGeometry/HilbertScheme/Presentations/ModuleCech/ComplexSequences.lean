import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.ComplexMaps
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.HomologySequences

/-! # Complex Sequences -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.ComplexSequences.ProjectiveCech

noncomputable section

/-! A short exact sequence of graded polynomial modules gives a short exact sequence of actual homogeneous Čech cochain complexes. -/

open _root_.MvPolynomial DirectSum _root_.CategoryTheory

universe u v w

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable {M N P : Type w}
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial σ R) N]
  [IsScalarTower R (MvPolynomial σ R) N]
variable [AddCommGroup P] [Module R P] [Module (MvPolynomial σ R) P]
  [IsScalarTower R (MvPolynomial σ R) P]
variable (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N) (ℙ : ℤ → Submodule R P)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℙ]
variable (f : M →ₗ[MvPolynomial σ R] N) (g : N →ₗ[MvPolynomial σ R] P)
variable (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hg : ∀ d m, m ∈ 𝒩 d → g m ∈ ℙ d)
variable (hex : Function.Exact f g)

def moduleCechComplexSequence (d : ℤ) : ShortComplex (CochainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (ComplexMaps.ProjectiveCech.moduleCechComplexMap R ℳ 𝒩 f hf d) (ComplexMaps.ProjectiveCech.moduleCechComplexMap R 𝒩 ℙ g hg d) (by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (Maps.ProjectiveCech.moduleCechMap_exact R f g hex _).mpr ⟨x.val, rfl⟩)

variable [Decomposition ℳ] [Decomposition 𝒩] [Decomposition ℙ]

theorem moduleCechComplexSequence_shortExact (hfinj : Function.Injective f) (hgsurj : Function.Surjective g)
    (d : ℤ) : (moduleCechComplexSequence R ℳ 𝒩 ℙ f g hf hg hex d).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact TermMaps.ProjectiveCech.moduleCechTermMap_exact R ℳ 𝒩 ℙ f g hf hg hex d q
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact TermMaps.ProjectiveCech.moduleCechTermMap_injective R ℳ 𝒩 f hf hfinj d q
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact TermMaps.ProjectiveCech.moduleCechTermMap_surjective R 𝒩 ℙ g hg hgsurj d q

include hf hg hex in
theorem moduleCech_homology_finite_of_exact [IsNoetherianRing R]
    (hfinj : Function.Injective f) (hgsurj : Function.Surjective g) (d : ℤ) (q : ℕ)
    [Module.Finite R ((CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R N 𝒩 d).homology q)]
    [Module.Finite R ((CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R M ℳ d).homology (q + 1))] :
    Module.Finite R ((CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R P ℙ d).homology q) := by
  let S := moduleCechComplexSequence R ℳ 𝒩 ℙ f g hf hg hex d
  let : Module.Finite R (S.X₂.homology q) :=
    inferInstanceAs (Module.Finite R ((CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R N 𝒩 d).homology q))
  let : Module.Finite R (S.X₁.homology (q + 1)) :=
    inferInstanceAs (Module.Finite R ((CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R M ℳ d).homology (q + 1)))
  exact Presentations.Finite.HomologySequences.finite_homology_of_shortExact R S
    (moduleCechComplexSequence_shortExact R ℳ 𝒩 ℙ f g hf hg hex hfinj hgsurj d) q

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.ComplexSequences.ProjectiveCech
