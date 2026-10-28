import OAI.AlgebraicGeometry.Comparison.Betti.MultivariableGermFactorization
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoordinateFlatness
import OAI.AlgebraicGeometry.Comparison.Betti.PolynomialFlatBaseChange

/-! # Multivariable Germ Flatness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MultivariableGermFlatness.AnalyticLocal

noncomputable section

/-! Actual evaluation of complex polynomials in all local coordinates
is flat in every finite dimension. -/

theorem mvPolynomialGermMap_zero_bijective (x : Fin 0 → ℂ) :
    Function.Bijective (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap x) := by
  have hC : Function.Surjective (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 0) ℂ) := by
    rw [← MvPolynomial.isEmptyAlgEquiv_symm_toRingHom]
    exact (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).symm.surjective
  constructor
  · intro P Q h
    obtain ⟨p, rfl⟩ := hC P
    obtain ⟨q, rfl⟩ := hC Q
    have he : p = q := by
      have hv := congrArg (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x) h
      simpa only [MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap_value, MvPolynomial.eval_C] using hv
    rw [he]
  · intro a
    obtain ⟨c, hc⟩ := NoetherianHolomorphicGerms.AnalyticLocal.holomorphicConstantHom_surjective x a
    exact ⟨MvPolynomial.C c, (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap_C x c).trans hc⟩

theorem mvPolynomialGermMap_flat (n : ℕ) (x : Fin n → ℂ) : (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap x).Flat := by
  induction n with
  | zero => exact RingHom.Flat.of_bijective (mvPolynomialGermMap_zero_bijective x)
  | succ n ih =>
    have hP := PolynomialFlatBaseChange.AnalyticLocal.polynomial_map_flat (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap (fun i : Fin n => x i.succ))
      (ih (fun i : Fin n => x i.succ))
    have hD := Holomorphic.CoordinateFlatness.AnalyticLocal.polynomialEvaluationGerm_flat (fun i : Fin n => x i.succ) (x 0)
    have hE : (MvPolynomial.finSuccEquiv ℂ n).toRingEquiv.toRingHom.Flat :=
      RingHom.Flat.of_bijective (MvPolynomial.finSuccEquiv ℂ n).bijective
    have h := (hE.comp hP).comp hD
    rw [← MultivariableGermFactorization.AnalyticLocal.mvPolynomialGermMap_fin_factorization n x] at h
    exact (RingHom.Flat.comp_iff_of_bijective_left (FinCoordinateGerms.AnalyticLocal.finCoordinateGermEquiv n x).bijective).mp h

end

end OAI.AlgebraicGeometry.Comparison.Betti.MultivariableGermFlatness.AnalyticLocal
