import Mathlib.RingTheory.AdjoinRoot

/-! # Polynomial Quotient -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.PolynomialQuotient.AnalyticLocal

noncomputable section

/-! Exact polynomial division makes the quotient by a monic relation
a finite module over the coefficient ring. -/

open _root_.Polynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem finite_quotient_of_polynomial_division (a : A) (P : R[X]) (hP : P.Monic)
    (hdivision : ∀ x : A, ∃ (Q : R[X]) (b : A), x = aeval a Q + aeval a P * b) :
    Module.Finite R (A ⧸ Ideal.span {aeval a P}) := by
  let I : Ideal A := Ideal.span {aeval a P}
  let π := Ideal.Quotient.mkₐ R I
  have hz : π (aeval a P) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hroot : aeval (π a) P = 0 := by
    rw [aeval_algHom_apply, hz]
  let f : AdjoinRoot P →ₐ[R] A ⧸ I := AdjoinRoot.liftAlgHom P (Algebra.ofId R _) (π a) hroot
  have hf : ∀ Q : R[X], f (AdjoinRoot.mk P Q) = π (aeval a Q) := by
    intro Q
    change aeval (π a) Q = π (aeval a Q)
    exact aeval_algHom_apply π a Q
  have hsur : Function.Surjective f := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨Q, b, hx⟩ := hdivision x
    refine ⟨AdjoinRoot.mk P Q, ?_⟩
    rw [hf]
    change π (aeval a Q) = π x
    rw [hx, map_add, map_mul, hz, zero_mul, add_zero]
  let : Module.Finite R (AdjoinRoot P) := hP.finite_adjoinRoot
  exact Module.Finite.of_surjective f.toLinearMap hsur

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.PolynomialQuotient.AnalyticLocal
