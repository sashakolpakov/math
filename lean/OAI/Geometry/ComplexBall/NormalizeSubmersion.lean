import OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall

/-! # Normalize Submersion -/

namespace OAI.Geometry.ComplexBall.NormalizeSubmersion.ArithmeticQuotient

noncomputable section

/-! Affine normalization of a negative vector is a holomorphic submersion.
A slice with fixed nonzero last coordinate gives an explicit right inverse. -/

open scoped Classical _root_.Manifold
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

def affineNormalize (z : ArithmeticQuotientEquationsData.Vec ℂ) : ArithmeticQuotientBoostBall.BallCoordinates := fun i => z i.castSucc / z 2

def affineSlice (c : ℂ) (w : ArithmeticQuotientBoostBall.BallCoordinates) : ArithmeticQuotientEquationsData.Vec ℂ := ![c * w 0, c * w 1, c]

lemma affineNormalize_slice (c : ℂ) (hc : c ≠ 0) (w : ArithmeticQuotientBoostBall.BallCoordinates) :
    affineNormalize (affineSlice c w) = w := by
  funext i
  fin_cases i <;> simp [affineNormalize, affineSlice, hc]

lemma affineSlice_normalize (z : ArithmeticQuotientEquationsData.Vec ℂ) (hz : z 2 ≠ 0) :
    affineSlice (z 2) (affineNormalize z) = z := by
  funext i
  fin_cases i <;> simp [affineNormalize, affineSlice] <;> field_simp

lemma differentiable_affineSlice (c : ℂ) : Differentiable ℂ (affineSlice c) := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i <;> simp [affineSlice] <;> fun_prop

lemma differentiableAt_affineNormalize (z : ArithmeticQuotientEquationsData.Vec ℂ) (hz : z 2 ≠ 0) :
    DifferentiableAt ℂ affineNormalize z := by
  have h : ContDiffAt ℂ 1 affineNormalize z := by
    apply contDiffAt_pi.mpr
    intro i
    exact (show ContDiffAt ℂ 1 (fun x : ArithmeticQuotientEquationsData.Vec ℂ => x i.castSucc) z by fun_prop).div
      (show ContDiffAt ℂ 1 (fun x : ArithmeticQuotientEquationsData.Vec ℂ => x 2) z by fun_prop) hz
  exact h.differentiableAt one_ne_zero

lemma affineNormalize_fderiv_surjective (z : ArithmeticQuotientEquationsData.Vec ℂ) (hz : z 2 ≠ 0) :
    Function.Surjective (fderiv ℂ affineNormalize z) := by
  let y := affineNormalize z
  have hslice : affineSlice (z 2) y = z := affineSlice_normalize z hz
  have hd : DifferentiableAt ℂ affineNormalize (affineSlice (z 2) y) := by
    rw [hslice]
    exact differentiableAt_affineNormalize z hz
  have he : affineNormalize ∘ affineSlice (z 2) = id :=
    funext (affineNormalize_slice (z 2) hz)
  have hc := fderiv_comp y hd (differentiable_affineSlice (z 2) y)
  rw [he, fderiv_id, hslice] at hc
  intro u
  refine ⟨fderiv ℂ (affineSlice (z 2)) y u, ?_⟩
  exact (congrArg (fun L => L u) hc).symm

end

end OAI.Geometry.ComplexBall.NormalizeSubmersion.ArithmeticQuotient
