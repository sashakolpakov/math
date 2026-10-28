import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Orientation
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-! # Complex Tangent -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ComplexTangent

/-!
# Local linear algebra for integration on complex submanifolds

These results concern actual alternating forms and linear maps. They supply
orientation invariance under complex coordinate changes and dimension bounds
for the restriction of forms to tangent planes. They do not define a global
integration current or assert a comparison with singular cohomology.
-/

section Dimension

variable {K V N : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup N] [Module K N]

/-- An alternating form of degree greater than the dimension is zero. -/
theorem alternating_eq_zero_of_degree_gt {n : ℕ}
    (ω : V [⋀^Fin n]→ₗ[K] N) (h : Module.finrank K V < n) : ω = 0 := by
  ext v
  apply ω.map_linearDependent
  intro hv
  exact (not_le_of_gt h) (by simpa using hv.fintype_card_le_finrank)

end Dimension

section Restriction

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Holomorphic alternating forms vanish on complex tangent planes of smaller
dimension than their degree. The map need not be injective. -/
theorem complexAlternating_pullback_eq_zero_of_degree_gt {n : ℕ}
    (ω : V [⋀^Fin n]→ₗ[ℂ] ℂ) (j : W →ₗ[ℂ] V)
    (h : Module.finrank ℂ W < n) : ω.compLinearMap j = 0 :=
  alternating_eq_zero_of_degree_gt (ω.compLinearMap j) h

end Restriction

section ContinuousRestriction

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

/-- The continuous-form version of the complex tangent-plane dimension bound. -/
theorem complexContinuousAlternating_pullback_eq_zero_of_degree_gt {n : ℕ}
    (ω : V [⋀^Fin n]→L[ℂ] ℂ) (j : W →L[ℂ] V)
    (h : Module.finrank ℂ W < n) : ω.compContinuousLinearMap j = 0 := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact alternating_eq_zero_of_degree_gt
    (ω.compContinuousLinearMap j).toAlternatingMap h

end ContinuousRestriction

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Restricting a complex-linear endomorphism to real scalars changes its
determinant to the squared complex norm of its original determinant. -/
theorem complexLinearMap_real_det (f : V →ₗ[ℂ] V) :
    (f.restrictScalars ℝ).det = Complex.normSq f.det := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- Invertible complex-linear coordinate changes have positive real Jacobian. -/
theorem complexLinearEquiv_real_det_pos (e : V ≃ₗ[ℂ] V) :
    0 < ((e : V →ₗ[ℂ] V).restrictScalars ℝ).det := by
  rw [complexLinearMap_real_det]
  exact Complex.normSq_pos.mpr e.isUnit_det'.ne_zero

variable [FiniteDimensional ℂ V]

/-- Thus a complex-linear change of coordinates preserves real orientation.
This is the local compatibility needed to orient a complex submanifold. -/
theorem complexLinearEquiv_preserves_real_orientation
    {ι : Type*} [Fintype ι] (o : Orientation ℝ V ι) (e : V ≃ₗ[ℂ] V)
    (h : Fintype.card ι = Module.finrank ℝ V) :
    Orientation.map ι (e.restrictScalars ℝ) o = o := by
  apply (o.map_eq_iff_det_pos (e.restrictScalars ℝ) h).2
  exact complexLinearEquiv_real_det_pos e

/-- Real alternating forms vanish above twice the complex tangent dimension. -/
theorem realAlternating_eq_zero_of_degree_gt_complex_dimension {n : ℕ}
    (ω : V [⋀^Fin n]→ₗ[ℝ] ℂ) (h : 2 * Module.finrank ℂ V < n) : ω = 0 := by
  apply alternating_eq_zero_of_degree_gt ω
  simpa only [finrank_real_of_complex] using h

end OAI.AlgebraicTopology.DeRham.Comparison.ComplexTangent
