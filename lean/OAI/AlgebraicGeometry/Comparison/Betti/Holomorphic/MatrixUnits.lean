import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionUnits
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Matrix Units -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.MatrixUnits

noncomputable section

/-! A holomorphic matrix invertible at a point has an actual holomorphic inverse nearby. -/

open _root_.TopologicalSpace

variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [Fintype ι] [DecidableEq ι] {U : Opens E}

def holomorphicFunctionEvaluation (x : U) : FunctionPure.holomorphicFunctions U →+* ℂ where
  toFun f := f.val x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem exists_restrict_holomorphicMatrix_isUnit (A : Matrix ι ι (FunctionPure.holomorphicFunctions U))
    (x : U) (hx : (A.map (holomorphicFunctionEvaluation x)).det ≠ 0) :
    ∃ (V : Opens E) (h : V ≤ U), (x : E) ∈ V ∧
      IsUnit (A.map (Restrictions.holomorphicFunctionRestrict h)) := by
  have hd : A.det.val x ≠ 0 := by
    change holomorphicFunctionEvaluation x A.det ≠ 0
    rwa [(holomorphicFunctionEvaluation x).map_det]
  obtain ⟨V, h, hxV, hdet⟩ := FunctionUnits.exists_restrict_holomorphicFunction_isUnit A.det x hd
  refine ⟨V, h, hxV, (Matrix.isUnit_iff_isUnit_det _).mpr ?_⟩
  exact ((Restrictions.holomorphicFunctionRestrict h).toRingHom.map_det A) ▸ hdet

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.MatrixUnits
