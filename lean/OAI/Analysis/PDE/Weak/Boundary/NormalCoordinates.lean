import OAI.Analysis.PDE.Weak.Boundary.OperatorEntries

noncomputable section
open Set
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem continuousLinearForm_exists_pivot (g : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ) (hg : g ≠ 0) :
    ∃ k : Fin (m+1), g (Pi.single k 1) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hg
  ext y
  have hy : y = ∑ j, y j • Pi.single j 1 := by
    ext j
    simp [Pi.single_apply]
  rw [hy, map_sum]
  simp only [map_smul, hn, smul_zero, Finset.sum_const_zero, zero_apply]

/-- A regular real normal can be made a coordinate without requiring an
orthogonal frame. The chosen sign maps a negative sublevel to a positive
coordinate halfspace. -/
theorem exists_coordinate_normalizer (g : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ) (hg : g ≠ 0) :
    ∃ (k : Fin (m+1)) (L : OAI.Analysis.PDE.Variational.CellCoordinates m ≃L[ℝ] OAI.Analysis.PDE.Variational.CellCoordinates m),
      ∀ y, (L y) k = -g y := by
  obtain ⟨k, hk⟩ := continuousLinearForm_exists_pivot g hg
  let e : OAI.Analysis.PDE.Variational.CellCoordinates m := Pi.single k 1
  let p : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ := ContinuousLinearMap.proj k
  let A : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] OAI.Analysis.PDE.Variational.CellCoordinates m :=
    ContinuousLinearMap.id ℝ _ + (-g - p).smulRight e
  let B : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] OAI.Analysis.PDE.Variational.CellCoordinates m :=
    ContinuousLinearMap.id ℝ _ + ((g e)⁻¹ • (-p - g)).smulRight e
  have hA (y) : A y = y + (-g y - y k) • e := rfl
  have hB (y) : B y = y + ((g e)⁻¹ * (-y k - g y)) • e := rfl
  have he : e k = 1 := by simp [e]
  have hge : g e ≠ 0 := hk
  have hab (y) : A (B y) = y := by
    rw [hA, hB]
    simp only [map_add, map_smul, smul_eq_mul, Pi.add_apply, Pi.smul_apply, he, mul_one]
    have hc : - (g y + (g e)⁻¹ * (-y k - g y) * g e) -
        (y k + (g e)⁻¹ * (-y k - g y)) = -((g e)⁻¹ * (-y k - g y)) := by
      field_simp
      ring
    rw [hc, neg_smul, add_neg_cancel_right]
  have hba (y) : B (A y) = y := by
    rw [hB, hA]
    simp only [map_add, map_smul, smul_eq_mul, Pi.add_apply, Pi.smul_apply, he, mul_one]
    have hc : (g e)⁻¹ * (-(y k + (-g y - y k)) -
        (g y + (-g y - y k) * g e)) = -(-g y - y k) := by
      field_simp
      ring
    rw [hc, neg_smul, add_neg_cancel_right]
  let L : OAI.Analysis.PDE.Variational.CellCoordinates m ≃L[ℝ] OAI.Analysis.PDE.Variational.CellCoordinates m :=
    { toLinearEquiv :=
        { toLinearMap := A.toLinearMap
          invFun := B
          left_inv := hba
          right_inv := hab }
      continuous_toFun := A.continuous
      continuous_invFun := B.continuous }
  refine ⟨k, L, ?_⟩
  intro y
  change (A y) k = -g y
  rw [hA]
  simp only [Pi.add_apply, Pi.smul_apply, he, smul_eq_mul, mul_one]
  ring

end OAI.Analysis.PDE.Weak
