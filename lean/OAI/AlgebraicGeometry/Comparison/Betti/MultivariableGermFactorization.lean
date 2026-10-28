import OAI.AlgebraicGeometry.Comparison.Betti.FinCoordinateGermNormalization
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Multivariable Germ Factorization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MultivariableGermFactorization.AnalyticLocal

noncomputable section

/-! The actual multivariable polynomial germ map factors through
coefficientwise polynomial extension under coordinate splitting. -/

theorem mvPolynomialGermMap_fin_factorization (n : ℕ) (x : Fin (n + 1) → ℂ) :
    (FinCoordinateGerms.AnalyticLocal.finCoordinateGermEquiv n x).toRingHom.comp (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap x) =
      (GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm (fun i : Fin n => x i.succ) (x 0)).comp
        ((Polynomial.mapRingHom (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap (fun i : Fin n => x i.succ))).comp
          (MvPolynomial.finSuccEquiv ℂ n).toRingEquiv.toRingHom) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change FinCoordinateGerms.AnalyticLocal.finCoordinateGermEquiv n x (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap x (MvPolynomial.C c)) =
      GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm (fun i : Fin n => x i.succ) (x 0)
        (Polynomial.map (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap (fun i : Fin n => x i.succ))
          (MvPolynomial.finSuccEquiv ℂ n (MvPolynomial.C c)))
    rw [MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap_C, FinCoordinateGermNormalization.AnalyticLocal.finCoordinateGermEquiv_constant]
    have hc : MvPolynomial.finSuccEquiv ℂ n (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
      simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    rw [hc, Polynomial.map_C, MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap_C]
    change Holomorphic.GermMaps.AnalyticLocal.holomorphicConstantHom ((fun i : Fin n => x i.succ), x 0) c =
      (Polynomial.C (Holomorphic.GermMaps.AnalyticLocal.holomorphicConstantHom (fun i : Fin n => x i.succ) c)).eval₂
        (GermPolynomialNe.AnalyticLocal.parameterInclusion (fun i : Fin n => x i.succ) (x 0))
        (GermPolynomialNe.AnalyticLocal.coordinateGerm (fun i : Fin n => x i.succ) (x 0))
    rw [Polynomial.eval₂_C]
    apply Subtype.ext
    rfl
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change FinCoordinateGerms.AnalyticLocal.finCoordinateGermEquiv n x (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap x (MvPolynomial.X 0)) =
        GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm (fun i : Fin n => x i.succ) (x 0)
          (Polynomial.map (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap (fun i : Fin n => x i.succ))
            (MvPolynomial.finSuccEquiv ℂ n (MvPolynomial.X 0)))
      rw [MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap_X, FinCoordinateGermNormalization.AnalyticLocal.finCoordinateGermEquiv_zero, MvPolynomial.finSuccEquiv_X_zero,
        Polynomial.map_X]
      change GermPolynomialNe.AnalyticLocal.coordinateGerm (fun i : Fin n => x i.succ) (x 0) =
        Polynomial.X.eval₂ (GermPolynomialNe.AnalyticLocal.parameterInclusion (fun i : Fin n => x i.succ) (x 0))
          (GermPolynomialNe.AnalyticLocal.coordinateGerm (fun i : Fin n => x i.succ) (x 0))
      rw [Polynomial.eval₂_X]
    · change FinCoordinateGerms.AnalyticLocal.finCoordinateGermEquiv n x (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap x (MvPolynomial.X j.succ)) =
        GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm (fun i : Fin n => x i.succ) (x 0)
          (Polynomial.map (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap (fun i : Fin n => x i.succ))
            (MvPolynomial.finSuccEquiv ℂ n (MvPolynomial.X j.succ)))
      rw [MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap_X, FinCoordinateGermNormalization.AnalyticLocal.finCoordinateGermEquiv_succ, MvPolynomial.finSuccEquiv_X_succ,
        Polynomial.map_C, MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap_X]
      change GermPolynomialNe.AnalyticLocal.parameterInclusion (fun i : Fin n => x i.succ) (x 0)
          (MultivariablePolynomialGerms.AnalyticLocal.coordinateFunctionGerm (fun i : Fin n => x i.succ) j) =
        (Polynomial.C (MultivariablePolynomialGerms.AnalyticLocal.coordinateFunctionGerm (fun i : Fin n => x i.succ) j)).eval₂
          (GermPolynomialNe.AnalyticLocal.parameterInclusion (fun i : Fin n => x i.succ) (x 0))
          (GermPolynomialNe.AnalyticLocal.coordinateGerm (fun i : Fin n => x i.succ) (x 0))
      rw [Polynomial.eval₂_C]

end

end OAI.AlgebraicGeometry.Comparison.Betti.MultivariableGermFactorization.AnalyticLocal
