import OAI.Analysis.PDE.Concentration.CovarianceLocal
import OAI.Analysis.PDE.Concentration.Physical.Current

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion
open scoped Matrix

def nullImaginaryProjection (d : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 →L[ℝ] (OAI.Analysis.Calculus.Current.Index d → ℂ) :=
  (ContinuousLinearMap.snd ℝ (OAI.Analysis.Calculus.Current.Index d → ℝ) (OAI.Analysis.Calculus.Current.Index d → ℂ)).comp (nullCoordinateProjection d)

theorem nullImaginaryProjection_apply (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    nullImaginaryProjection d x = (nullCoordinateProjection d x).2 := rfl

theorem nullImaginaryProjection_coordinateVector (d : ℕ) (i : Fin (d + 2)) (α : Fin 3) :
    nullImaginaryProjection d (OAI.Analysis.PDE.Dirichlet.coordinateVector (i, α)) =
      OAI.Analysis.Calculus.Quaternion.imaginaryDirection (nullIndexEquiv d i) α := by
  rw [nullImaginaryProjection_apply, nullCoordinateProjection_coordinateVector]
  fin_cases α <;> simp [OAI.Analysis.Calculus.Current.currentDirection, OAI.Analysis.Calculus.Quaternion.imaginaryDirection, OAI.Analysis.Calculus.Quaternion.imaginarySlot]
  ext j
  by_cases hj : j = nullIndexEquiv d i <;> simp [hj]

theorem quaternionHessian_nullImaginary {d : ℕ} {f : (OAI.Analysis.Calculus.Current.Index d → ℂ) → ℝ}
    {U : Set (OAI.Analysis.Calculus.Current.Index d → ℂ)} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : nullImaginaryProjection d x ∈ U) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (f ∘ nullImaginaryProjection d) x =
      nullMatrixReindex d (OAI.Analysis.Calculus.Quaternion.imaginaryHessian f (nullImaginaryProjection d x)) := by
  apply Matrix.ext
  intro a b
  change OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (f ∘ nullImaginaryProjection d) x a b =
    OAI.Analysis.Calculus.Quaternion.imaginaryHessian f (nullImaginaryProjection d x) (nullIndexEquiv d a) (nullIndexEquiv d b)
  simp only [OAI.Analysis.PDE.Dirichlet.quaternionHessian, OAI.Analysis.PDE.Dirichlet.realHessian, OAI.Analysis.Calculus.Quaternion.hessianMap, OAI.Analysis.Calculus.Quaternion.imaginaryHessian]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  rw [second_fderiv_comp_linear_on (nullImaginaryProjection d) hU hf hx,
    nullImaginaryProjection_coordinateVector, nullImaginaryProjection_coordinateVector]

/-- Full spacetime covariance of the actual differentiated Hessian of a
function of the source's complex null coordinates, locally on its domain. -/
theorem quaternionHessian_physical_null {d : ℕ} {f : (OAI.Analysis.Calculus.Current.Index d → ℂ) → ℝ}
    {U : Set (OAI.Analysis.Calculus.Current.Index d → ℂ)} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : (physicalToNullCurrentPoint d x).2 ∈ U) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => f (physicalToNullCurrentPoint d y).2) x =
      matrixConjugationCLM (nullRotation d)
        (nullMatrixReindex d (OAI.Analysis.Calculus.Quaternion.imaginaryHessian f (physicalToNullCurrentPoint d x).2)) := by
  have hpre : IsOpen ((nullImaginaryProjection d) ⁻¹' U) :=
    hU.preimage (nullImaginaryProjection d).continuous
  have hfc := hf.comp_continuousLinearMap (nullImaginaryProjection d)
  have hcov := quaternionHessian_slot_comp_on OAI.Analysis.Calculus.Quaternion.threeSlots hpre hfc (nullRotation d) x hx
  change OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
    ((f ∘ nullImaginaryProjection d) ∘ OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d))) x = _
  rw [hcov]
  change matrixConjugationCLM (nullRotation d)
    (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (f ∘ nullImaginaryProjection d)
      (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) x)) = _
  congr 1
  exact quaternionHessian_nullImaginary hU hf _ hx

end OAI.Analysis.PDE.Concentration
