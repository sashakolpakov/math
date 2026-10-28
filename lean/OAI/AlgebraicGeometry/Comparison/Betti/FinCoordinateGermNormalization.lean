import OAI.AlgebraicGeometry.Comparison.Betti.FinCoordinateGerms
import OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialNe

/-! # Fin Coordinate Germ Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FinCoordinateGermNormalization.AnalyticLocal

noncomputable section

/-! The actual coordinate splitting preserves constants and identifies
the first and remaining coordinate germs explicitly. -/

theorem finCoordinateGermEquiv_constant (n : ℕ) (x : Fin (n + 1) → ℂ) (c : ℂ) :
    FinCoordinateGerms.AnalyticLocal.finCoordinateGermEquiv n x (Holomorphic.GermMaps.AnalyticLocal.holomorphicConstantHom x c) =
      Holomorphic.GermMaps.AnalyticLocal.holomorphicConstantHom ((fun i : Fin n => x i.succ), x 0) c := by
  apply Subtype.ext
  exact GermCoordinateEquiv.AnalyticLocal.holomorphicGermEquiv_val (FinCoordinateGerms.AnalyticLocal.finCoordinateEquiv n).toEquiv (FinCoordinateGerms.AnalyticLocal.finCoordinateEquiv n).differentiable
    (FinCoordinateGerms.AnalyticLocal.finCoordinateEquiv n).symm.differentiable x (fun _ => c)
    isOpen_univ (Set.mem_univ x) (differentiableOn_const c)

theorem finCoordinateGermEquiv_zero (n : ℕ) (x : Fin (n + 1) → ℂ) :
    FinCoordinateGerms.AnalyticLocal.finCoordinateGermEquiv n x (MultivariablePolynomialGerms.AnalyticLocal.coordinateFunctionGerm x 0) =
      GermPolynomialNe.AnalyticLocal.coordinateGerm (fun i : Fin n => x i.succ) (x 0) := by
  apply Subtype.ext
  exact GermCoordinateEquiv.AnalyticLocal.holomorphicGermEquiv_val (FinCoordinateGerms.AnalyticLocal.finCoordinateEquiv n).toEquiv (FinCoordinateGerms.AnalyticLocal.finCoordinateEquiv n).differentiable
    (FinCoordinateGerms.AnalyticLocal.finCoordinateEquiv n).symm.differentiable x (fun y => y 0)
    isOpen_univ (Set.mem_univ x) (differentiable_apply 0).differentiableOn

theorem finCoordinateGermEquiv_succ (n : ℕ) (x : Fin (n + 1) → ℂ) (i : Fin n) :
    FinCoordinateGerms.AnalyticLocal.finCoordinateGermEquiv n x (MultivariablePolynomialGerms.AnalyticLocal.coordinateFunctionGerm x i.succ) =
      GermPolynomialNe.AnalyticLocal.parameterInclusion (fun j : Fin n => x j.succ) (x 0)
        (MultivariablePolynomialGerms.AnalyticLocal.coordinateFunctionGerm (fun j : Fin n => x j.succ) i) := by
  apply Subtype.ext
  exact GermCoordinateEquiv.AnalyticLocal.holomorphicGermEquiv_val (FinCoordinateGerms.AnalyticLocal.finCoordinateEquiv n).toEquiv (FinCoordinateGerms.AnalyticLocal.finCoordinateEquiv n).differentiable
    (FinCoordinateGerms.AnalyticLocal.finCoordinateEquiv n).symm.differentiable x (fun y => y i.succ)
    isOpen_univ (Set.mem_univ x) (differentiable_apply i.succ).differentiableOn

end

end OAI.AlgebraicGeometry.Comparison.Betti.FinCoordinateGermNormalization.AnalyticLocal
