import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Energy Coercivity -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.EnergyCoercivity

noncomputable section

/-! A genuine squared-norm energy estimate passes from a linear range to its topological closure. -/

variable {S H X Y Z : Type*} [AddCommGroup S] [Module ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem linearRangeClosure_inclusion_dense (L : S →ₗ[ℂ] H) :
    DenseRange (L.codRestrict (LinearMap.range L).topologicalClosure
      (fun s => (LinearMap.range L).le_topologicalClosure ⟨s, rfl⟩)) := by
  have hd : DenseRange (Set.inclusion (show Set.range L ⊆ closure (Set.range L) from subset_closure)) :=
    (denseRange_inclusion_iff subset_closure).mpr Set.Subset.rfl
  exact hd.comp (Set.rangeFactorization_surjective (f := L)).denseRange (continuous_inclusion subset_closure)

theorem energyCoercivity_on_range_closure (L : S →ₗ[ℂ] H)
    (A : H →L[ℂ] X) (B : H →L[ℂ] Y) (C : H →L[ℂ] Z)
    (hL : ∀ s, ‖A (L s)‖ ^ 2 ≤ ‖B (L s)‖ ^ 2 + ‖C (L s)‖ ^ 2)
    {v : H} (hv : v ∈ (LinearMap.range L).topologicalClosure) :
    ‖A v‖ ^ 2 ≤ ‖B v‖ ^ 2 + ‖C v‖ ^ 2 := by
  have hclosed : IsClosed {w : H | ‖A w‖ ^ 2 ≤ ‖B w‖ ^ 2 + ‖C w‖ ^ 2} :=
    isClosed_le (A.continuous.norm.pow 2) ((B.continuous.norm.pow 2).add (C.continuous.norm.pow 2))
  apply closure_minimal (s := (LinearMap.range L : Set H)) _ hclosed hv
  rintro _ ⟨s, rfl⟩
  exact hL s

theorem energySource_opNorm_of_twice_sq (A : H →L[ℂ] X)
    (hA : ∀ v, 2 * ‖A v‖ ^ 2 ≤ ‖v‖ ^ 2) : ‖A‖ ≤ Real.sqrt (1 / 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hh := hA v
  linarith only [hh]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.EnergyCoercivity
