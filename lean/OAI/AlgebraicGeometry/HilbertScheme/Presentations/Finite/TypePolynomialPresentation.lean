import Mathlib.RingTheory.FiniteType

/-! # Type Polynomial Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.TypePolynomialPresentation

noncomputable section

/-! A finite-type algebra has a polynomial presentation with a nonempty
finite variable set, including the case where no generators are needed. -/

open _root_.MvPolynomial

universe u v
variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

theorem finiteType_polynomial_presentation_succ :
    ∃ n : ℕ, ∃ f : MvPolynomial (Fin (n + 1)) R →ₐ[R] S, Function.Surjective f := by
  classical
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  let q : MvPolynomial (Fin (n + 1)) R →ₐ[R] S :=
    MvPolynomial.aeval (Fin.lastCases 0 (fun i => f (X i)))
  have hq : q.comp (MvPolynomial.rename Fin.castSucc) = f := by
    ext i
    simp [q]
  refine ⟨n, q, ?_⟩
  intro s
  obtain ⟨p, hp⟩ := hf s
  exact ⟨MvPolynomial.rename Fin.castSucc p,
    (DFunLike.congr_fun hq p).trans hp⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.TypePolynomialPresentation
