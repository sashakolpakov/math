import Mathlib.RingTheory.FiniteType

/-! # Generators -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.Generators

noncomputable section

/-!
# IntegralComparison: finite polynomial coordinates for finite-type algebras

Finite type supplies finitely many actual algebra generators. Their
evaluation map is surjective; the presentation is not assumed as data.
-/

universe u

variable (k C : Type u) [CommRing k] [CommRing C] [Algebra k C] [Algebra.FiniteType k C]

theorem exists_generators : ∃ (σ : Type u) (_ : Fintype σ) (x : σ → C),
    Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] C) := by
  obtain ⟨σ, hσ, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp
    (inferInstance : Algebra.FiniteType k C)
  refine ⟨σ, hσ, fun i => f (MvPolynomial.X i), ?_⟩
  have he : MvPolynomial.aeval (fun i => f (MvPolynomial.X i)) = f := by
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X _ i
  rwa [he]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.Generators
