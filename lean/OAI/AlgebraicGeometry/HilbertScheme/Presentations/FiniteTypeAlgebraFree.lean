import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GenericPolynomialQuotientFree
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.TypePolynomialPresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartBaseChange

/-! # Finite Type Algebra Free -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiniteTypeAlgebraFree

noncomputable section

/-! Every finite-type algebra over a domain is a free module after
inverting one nonzero base element. The module rank may be infinite. -/

open TensorProduct

universe u v
variable (R : Type u) [CommRing R] [IsDomain R]
variable (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

theorem exists_generic_free_finiteType_algebra :
    ∃ s : R, s ≠ 0 ∧ Module.Free (Localization.Away s) (Localization.Away s ⊗[R] S) := by
  obtain ⟨n, f, hf⟩ := Finite.TypePolynomialPresentation.finiteType_polynomial_presentation_succ R S
  let I := RingHom.ker f
  obtain ⟨s, hs, hfree⟩ := GenericPolynomialQuotientFree.GradedHilbert.exists_generic_free_polynomial_quotient I
  let A := Localization.Away s
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let e₁ := Affine.ChartBaseChange.GradedHilbert.polynomialQuotientBaseChangeEquiv (S := A) I
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) e
  let : Module.Free A (Hilbert.Polynomial.GradedHilbert.CoordinateRing A n ⧸
      I.map (MvPolynomial.map (algebraMap R A))) := hfree
  let : Module.Free A (A ⊗[R] (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I)) :=
    Module.Free.of_equiv e₁.symm.toLinearEquiv
  exact ⟨s, hs, Module.Free.of_equiv e₂.toLinearEquiv⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiniteTypeAlgebraFree
