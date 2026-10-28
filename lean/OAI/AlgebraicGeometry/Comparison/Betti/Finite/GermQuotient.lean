import OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialDivision
import OAI.AlgebraicGeometry.Comparison.Betti.GermPreparation
import OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialNe
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.PolynomialQuotient

/-! # Germ Quotient -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.GermQuotient.AnalyticLocal

noncomputable section

/-! A vertically regular holomorphic germ defines a finite algebra over
the actual ring of holomorphic parameter germs. -/

open _root_.Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

instance parameterGermAlgebra (x : E) (c : ℂ) :
    Algebra (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) := (GermPolynomialNe.AnalyticLocal.parameterInclusion x c).toAlgebra

theorem polynomialEvaluationGerm_eq_aeval (x : E) (c : ℂ) (P : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X]) :
    GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c P = aeval (GermPolynomialNe.AnalyticLocal.coordinateGerm x c) P := rfl

theorem distinguished_germ_quotient_finite [FiniteDimensional ℂ E]
    (x : E) (c : ℂ) (P : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X]) (hP : P.Monic)
    (hcenter : P.map (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x) = (X - C c) ^ P.natDegree) :
    Module.Finite (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)
      (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c) ⧸ Ideal.span {GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c P}) := by
  apply PolynomialQuotient.AnalyticLocal.finite_quotient_of_polynomial_division (GermPolynomialNe.AnalyticLocal.coordinateGerm x c) P hP
  intro a
  obtain ⟨b, S, _, hdivision⟩ := GermPolynomialDivision.AnalyticLocal.germ_polynomial_division x c P hP hcenter a
  exact ⟨S, b, hdivision⟩

theorem regular_germ_quotient_finite {n : ℕ} (x : Fin n → ℂ) (c : ℂ)
    (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) (ha : GermPreparation.AnalyticLocal.verticalRestriction x c a ≠ 0) :
    Module.Finite (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c) ⧸ Ideal.span {a}) := by
  obtain ⟨P, u, hP, hcenter, hu, hfactor⟩ := GermPreparation.AnalyticLocal.germ_weierstrass_preparation x c a ha
  rw [hfactor, Ideal.span_singleton_mul_right_unit hu]
  exact distinguished_germ_quotient_finite x c P hP hcenter

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.GermQuotient.AnalyticLocal
