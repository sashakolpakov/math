import Mathlib

/-! # Lattice Covolume Transport -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LatticeCovolumeTransport

noncomputable section

/-! Determinant-one real linear changes preserve lattice covolume. -/

open scoped Classical
open _root_.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem linearEquiv_measurePreserving_of_det_one (e : E ≃ₗ[ℝ] E) (he : e.toLinearMap.det = 1)
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] : MeasurePreserving e μ μ := by
  refine ⟨e.toLinearMap.continuous_of_finiteDimensional.measurable, ?_⟩
  have hn : e.toLinearMap.det ≠ 0 := he ▸ one_ne_zero
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hn
  rw [he, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at hm
  exact hm

theorem lattice_covolume_map_det_one (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (e : E ≃ₗ[ℝ] E) (he : e.toLinearMap.det = 1)
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    ZLattice.covolume (L.map (e.toLinearMap.restrictScalars ℤ)) μ = ZLattice.covolume L μ := by
  let c := e.toContinuousLinearEquiv
  have heq : L.map (e.toLinearMap.restrictScalars ℤ) = ZLattice.comap ℝ L c.symm.toLinearMap := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e.symm (e y) ∈ L
      rw [LinearEquiv.symm_apply_apply]
      exact hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  have hi : e.symm.toLinearMap.det = 1 := by
    rw [LinearEquiv.det_coe_symm, he, inv_one]
  have hp : MeasurePreserving c.symm μ μ := linearEquiv_measurePreserving_of_det_one e.symm hi μ
  rw [heq]
  exact ZLattice.covolume_comap L μ μ hp

end

end OAI.NumberTheory.Quaternion.Arithmetic.LatticeCovolumeTransport
