import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Linear Coordinate Direction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.LinearCoordinateDirection.AnalyticLocal

noncomputable section

/-! A nonzero complex direction can be made a coordinate axis by a
continuous linear change of coordinates. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_coordinate_linear_equiv (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ e : E ≃L[ℂ] E, e u = v := by
  let eu := LinearEquiv.toSpanNonzeroSingleton ℂ E u hu
  let ev := LinearEquiv.toSpanNonzeroSingleton ℂ E v hv
  let f := eu.symm.trans ev
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g.toContinuousLinearEquiv, ?_⟩
  change g u = v
  calc
    g u = g (eu 1) := by simp [eu]
    _ = f (eu 1) := (hg (eu 1)).symm
    _ = v := by simp [f, ev]

end

end OAI.AlgebraicGeometry.Comparison.Betti.LinearCoordinateDirection.AnalyticLocal
