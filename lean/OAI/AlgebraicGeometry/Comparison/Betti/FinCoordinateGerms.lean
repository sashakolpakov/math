import OAI.AlgebraicGeometry.Comparison.Betti.GermCoordinateEquiv
import OAI.AlgebraicGeometry.Comparison.Betti.MultivariablePolynomialGerms
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Fin Coordinate Germs -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FinCoordinateGerms.AnalyticLocal

noncomputable section

/-! Splitting the first coordinate gives a concrete equivalence of
holomorphic local rings in successive dimensions. -/

def finCoordinateLinearEquiv (n : ℕ) : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] ((Fin n → ℂ) × ℂ) where
  toFun y := (fun i => y i.succ, y 0)
  invFun p := Fin.cases p.2 p.1
  left_inv y := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by cases p; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finCoordinateEquiv (n : ℕ) : (Fin (n + 1) → ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ) :=
  (finCoordinateLinearEquiv n).toContinuousLinearEquiv

def finCoordinateGermEquiv (n : ℕ) (x : Fin (n + 1) → ℂ) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm ((fun i : Fin n => x i.succ), x 0) :=
  GermCoordinateEquiv.AnalyticLocal.holomorphicGermEquiv (finCoordinateEquiv n).toEquiv (finCoordinateEquiv n).differentiable
    (finCoordinateEquiv n).symm.differentiable x

end

end OAI.AlgebraicGeometry.Comparison.Betti.FinCoordinateGerms.AnalyticLocal
