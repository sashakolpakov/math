import OAI.NumberTheory.ArithmeticGroups.Lattices.VolumePreservingOperatorUnits
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Volume Normalized Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeNormalizedCoordinates.Construction

noncomputable section

/-! A scalar multiple normalizes a real change of basis to absolute
determinant one without changing its conjugation of endomorphisms. -/

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

def scalarCoordinateEquiv (c : ℝ) (hc : c ≠ 0) : L ≃L[ℝ] L :=
  (LinearEquiv.smulOfNeZero ℝ L c hc).toContinuousLinearEquiv

theorem scalarCoordinateEquiv_apply (c : ℝ) (hc : c ≠ 0) (x : L) :
    scalarCoordinateEquiv c hc x = c • x := rfl

theorem scalarCoordinateEquiv_symm_apply (c : ℝ) (hc : c ≠ 0) (x : L) :
    (scalarCoordinateEquiv c hc).symm x = c⁻¹ • x := rfl

theorem scalarCoordinateEquiv_conjugation (c : ℝ) (hc : c ≠ 0) (X : L →L[ℝ] L) :
    (scalarCoordinateEquiv c hc).conjContinuousAlgEquiv X = X := by
  ext x
  change c • X (c⁻¹ • x) = X x
  rw [map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem exists_volume_normalized_coordinates (e : L ≃L[ℝ] L) :
    ∃ f : L ≃L[ℝ] L, |f.toLinearMap.det| = 1 ∧
      f.conjContinuousAlgEquiv = e.conjContinuousAlgEquiv := by
  by_cases hn : Module.finrank ℝ L = 0
  · let : Subsingleton L := (Module.finrank_zero_iff).mp hn
    exact ⟨e, by rw [LinearMap.det_eq_one_of_subsingleton, abs_one], rfl⟩
  · let D := |e.toLinearMap.det|
    have hD : 0 < D := abs_pos.mpr e.toLinearEquiv.isUnit_det'.ne_zero
    let c := Real.exp (-Real.log D / (Module.finrank ℝ L : ℝ))
    have hc : 0 < c := Real.exp_pos _
    have hn' : (Module.finrank ℝ L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hp : c ^ Module.finrank ℝ L = D⁻¹ := by
      rw [show c = Real.exp (-Real.log D / (Module.finrank ℝ L : ℝ)) from rfl,
        ← Real.exp_nat_mul]
      rw [show (Module.finrank ℝ L : ℝ) * (-Real.log D / (Module.finrank ℝ L : ℝ)) =
        -Real.log D by field_simp]
      rw [Real.exp_neg, Real.exp_log hD]
    let f := e.trans (scalarCoordinateEquiv c hc.ne')
    refine ⟨f, ?_, ?_⟩
    · have he : f.toLinearMap = c • e.toLinearMap := by ext x; rfl
      rw [he, LinearMap.det_smul, abs_mul, abs_pow, abs_of_pos hc, hp]
      exact inv_mul_cancel₀ hD.ne'
    · ext X x
      change ((scalarCoordinateEquiv c hc.ne').conjContinuousAlgEquiv
        (e.conjContinuousAlgEquiv X)) x = _
      rw [scalarCoordinateEquiv_conjugation]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeNormalizedCoordinates.Construction
