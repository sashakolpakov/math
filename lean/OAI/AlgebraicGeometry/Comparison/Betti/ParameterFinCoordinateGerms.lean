import OAI.AlgebraicGeometry.Comparison.Betti.FinCoordinateGerms
import OAI.AlgebraicGeometry.Comparison.Betti.GermSliceDivision

/-! # Parameter Fin Coordinate Germs -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ParameterFinCoordinateGerms.AnalyticLocal

noncomputable section

/-! Splitting one normal coordinate in a product preserves the actual holomorphic germ ring. -/

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

def parameterFinCoordinateLinearEquiv (n : ℕ) :
    (E × (Fin (n + 1) → ℂ)) ≃ₗ[ℂ] ((E × (Fin n → ℂ)) × ℂ) where
  toFun p := ((p.1, fun i => p.2 i.succ), p.2 0)
  invFun p := (p.1.1, Fin.cases p.2 p.1.2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by rcases p with ⟨⟨x, z⟩, c⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def parameterFinCoordinateEquiv (n : ℕ) :
    (E × (Fin (n + 1) → ℂ)) ≃L[ℂ] ((E × (Fin n → ℂ)) × ℂ) :=
  (parameterFinCoordinateLinearEquiv E n).toContinuousLinearEquiv

def parameterFinCoordinateGermEquiv (n : ℕ) (x : E) (z : Fin (n + 1) → ℂ) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, z) ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm ((x, fun i : Fin n => z i.succ), z 0) :=
  GermCoordinateEquiv.AnalyticLocal.holomorphicGermEquiv (parameterFinCoordinateEquiv E n).toEquiv
    (parameterFinCoordinateEquiv E n).differentiable (parameterFinCoordinateEquiv E n).symm.differentiable (x, z)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ParameterFinCoordinateGerms.AnalyticLocal
