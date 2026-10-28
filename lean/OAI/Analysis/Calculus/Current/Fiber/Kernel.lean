import OAI.Analysis.Calculus.Current.Fiber

namespace OAI.Analysis.Calculus.Current

noncomputable section
open scoped Matrix

/-- The exact Jacobian row of `P_i / Y`. -/
def ratioRow {d : ℕ} (z : Index d → ℂ) (i : Fin d) : Index d → ℂ
  | none => -ratio z i / z none
  | some none => 0
  | some (some j) => if j = i then 1 / z none else 0

theorem ratioRow_apply {d : ℕ} (z h : Index d → ℂ) (hY : z none ≠ 0) (i : Fin d) :
    (∑ b, ratioRow z i b * h b) = ratioSlope z h i := by
  simp [Fintype.sum_option, ratioRow, ratioSlope, ratio]
  field_simp
  ring

def fiberJacobian {d : ℕ} (w a : ℝ) (z : Index d → ℂ) :
    Matrix (Option (Fin d)) (Index d) ℂ
  | none, b => (10 / (a : ℂ)) * phaseRow (ratio z) b
  | some i, b => (1 / (w : ℂ)) * ratioRow z i b

theorem hasDerivAt_ratio_complexLine {d : ℕ} (z h : Index d → ℂ)
    (hY : z none ≠ 0) (i : Fin d) :
    HasDerivAt (fun t : ℂ => ratio (fun b => z b + t * h b) i) (ratioSlope z h i) 0 := by
  have hz (b : Index d) : HasDerivAt (fun t : ℂ => z b + t * h b) (h b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (h b)).const_add (z b)
  simpa [ratio, ratioSlope] using (hz (some (some i))).fun_div (hz none) (by simpa using hY)

/-- Each row really differentiates the stated holomorphic fiber map. -/
theorem hasDerivAt_fiberMap_complexLine {d : ℕ} (w a : ℝ) (z h : Index d → ℂ)
    (hY : z none ≠ 0) (i : Option (Fin d)) :
    HasDerivAt (fun t : ℂ => fiberMap w a (fun b => z b + t * h b) i)
      ((fiberJacobian w a z *ᵥ h) i) 0 := by
  cases i with
  | none =>
    convert ((hasDerivAt_phi_line z h hY).const_mul (10 : ℂ)).div_const (a : ℂ) using 1
    · rfl
    · simp only [Matrix.mulVec, dotProduct, fiberJacobian, mul_assoc, ← Finset.mul_sum]
      ring
  | some i =>
    convert (hasDerivAt_ratio_complexLine z h hY i).div_const (w : ℂ) using 1
    · rfl
    · simp only [Matrix.mulVec, dotProduct, fiberJacobian, mul_assoc, ← Finset.mul_sum]
      rw [ratioRow_apply z h hY i]
      ring

/-- The unique free direction of the full fiber Jacobian, normalized by `dY = 1`. -/
def fiberKernelVector {d : ℕ} (z : Index d → ℂ) : Index d → ℂ
  | none => 1
  | some none => -fiberQuadratic (ratio z) / 2
  | some (some i) => ratio z i

theorem fiberKernelVector_eq_tangent {d : ℕ} (z : Index d → ℂ) :
    fiberKernelVector z = tangentVector (ratio z) (ratio z) := by
  funext b
  cases b with
  | none => rfl
  | some b =>
    cases b with
    | none => rfl
    | some i => simp [fiberKernelVector, tangentVector]

theorem fiberKernelVector_ne_zero {d : ℕ} (z : Index d → ℂ) : fiberKernelVector z ≠ 0 := by
  intro h
  have h0 := congrFun h none
  norm_num [fiberKernelVector] at h0

theorem fiberJacobian_kernel {d : ℕ} (w a : ℝ) (z : Index d → ℂ) :
    fiberJacobian w a z *ᵥ fiberKernelVector z = 0 := by
  funext i
  cases i with
  | none =>
    simp only [Matrix.mulVec, dotProduct, fiberJacobian, mul_assoc, ← Finset.mul_sum,
      fiberKernelVector_eq_tangent, background_tangent, mul_zero, Pi.zero_apply]
  | some i =>
    simp [Matrix.mulVec, dotProduct, fiberJacobian, Fintype.sum_option, ratioRow,
      fiberKernelVector]
    ring

/-- No additional full-space null directions are hidden by the coordinates. -/
theorem fiberJacobian_kernel_unique {d : ℕ} (w a : ℝ) (z h : Index d → ℂ)
    (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hJ : fiberJacobian w a z *ᵥ h = 0) :
    h = fun b => fiberKernelVector z b * h none := by
  have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hx (i : Fin d) : h (some (some i)) = ratio z i * h none := by
    have he := congrFun hJ (some i)
    have hr : (1 / (w : ℂ)) * ratioSlope z h i = 0 := by
      simpa only [Matrix.mulVec, dotProduct, fiberJacobian, mul_assoc, ← Finset.mul_sum,
        ratioRow_apply z h hY i, Pi.zero_apply] using he
    have hs := (mul_eq_zero.mp hr).resolve_left (div_ne_zero one_ne_zero hwC)
    unfold ratioSlope at hs
    unfold ratio
    field_simp at hs ⊢
    linear_combination hs
  have hp : (∑ b, phaseRow (ratio z) b * h b) = 0 := by
    have he := congrFun hJ none
    have hr : (10 / (a : ℂ)) * (∑ b, phaseRow (ratio z) b * h b) = 0 := by
      simpa only [Matrix.mulVec, dotProduct, fiberJacobian, mul_assoc, ← Finset.mul_sum,
        Pi.zero_apply] using he
    exact (mul_eq_zero.mp hr).resolve_left (div_ne_zero (by norm_num) haC)
  have hs : h (some none) = (-fiberQuadratic (ratio z) / 2) * h none := by
    simp only [Fintype.sum_option, phaseRow, one_mul] at hp
    simp_rw [hx] at hp
    have hsum : (∑ i, ratio z i * (ratio z i * h none)) =
        fiberQuadratic (ratio z) * h none := by
      simp only [fiberQuadratic, Finset.sum_mul, mul_assoc]
    rw [hsum] at hp
    change _ + (_ + _) = 0 at hp
    unfold fiberQuadratic at hp ⊢
    linear_combination hp
  funext b
  cases b with
  | none => simp [fiberKernelVector]
  | some b =>
    cases b with
    | none => exact hs
    | some i => exact hx i

/-- The Jacobian is injective on variations with fixed physical time.
In null coordinates these are precisely the directions `dY = dS₁`. -/
theorem fiberJacobian_spatial_injective {d : ℕ} (w a : ℝ) (z h : Index d → ℂ)
    (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hD : fiberDenominator (ratio z) ≠ 0)
    (htime : h none = h (some none)) (hJ : fiberJacobian w a z *ᵥ h = 0) : h = 0 := by
  have hu := fiberJacobian_kernel_unique w a z h hw ha hY hJ
  have hs := congrFun hu (some none)
  change h (some none) = (-fiberQuadratic (ratio z) / 2) * h none at hs
  have hz : fiberDenominator (ratio z) * h none = 0 := by
    unfold fiberDenominator
    linear_combination htime + hs
  have h0 := (mul_eq_zero.mp hz).resolve_left hD
  rw [hu]
  simp only [h0, mul_zero]
  rfl

end
end OAI.Analysis.Calculus.Current
