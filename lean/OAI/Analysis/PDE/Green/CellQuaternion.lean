import OAI.Analysis.PDE.Green.EuclideanCell
import OAI.Analysis.PDE.Green.PencilIntegral

/-! Quaternionic second Green identities on periodic cells. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise

theorem quaternion_current_second_green_cell {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hAh : ∀ x, (A x).IsHermitian)
    (hdiv : ∀ x j, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0)
    {r u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hnormal : ∀ x, r x = 0 → (OAI.Analysis.PDE.Dirichlet.quaternionForm (A x) (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x)).re = 0)
    (hface : CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) u v)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      v x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  have hK (p q : Fin n × Fin s) :
      ContDiff ℝ 1 (fun x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) :=
    (realCoefficientCLM e p q).contDiff.comp hA
  have hKs (p q : Fin n × Fin s) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q = OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) q p :=
    (congrFun (congrFun (OAI.Analysis.Calculus.Quaternion.realCoefficients_isSymm e (A x) (hAh x)) p) q).symm
  have hd (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (q : Fin n × Fin s) :
      (∑ p, fderiv ℝ (fun y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) = 0 := by
    simp_rw [fderiv_realCoefficient e _ _ (hA.differentiable (by norm_num) x)]
    exact OAI.Analysis.Calculus.Quaternion.realCoefficients_divergence_zero e _ (hdiv x) q
  have hn (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (hx : r x = 0) :
      (∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q *
        (fderiv ℝ r x (OAI.Analysis.PDE.Dirichlet.coordinateVector p) * fderiv ℝ r x (OAI.Analysis.PDE.Dirichlet.coordinateVector q))) = 0 := by
    rw [realCoefficients_quadratic]
    exact hnormal x hx
  have h := real_operator_second_green_cell c a b hab
    (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) hK hu hv hr hKs hd hrne huz hn hface
  have hform (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hf : ContDiff ℝ 2 f) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x) =
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q * OAI.Analysis.PDE.Dirichlet.realHessian f x p q :=
    realTrace_hessianMap (A x) e (OAI.Analysis.PDE.Dirichlet.realHessian f x) (OAI.Analysis.PDE.Dirichlet.realHessian_isSymm hf.contDiffAt)
  simpa only [hform u hu, hform v hv, OAI.Analysis.PDE.Dirichlet.realHessian, OAI.Analysis.PDE.Dirichlet.coordinateVector] using h

theorem moore_cofactor_second_green_cell {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {ψ r u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hnormal : ∀ x, r x = 0 → (OAI.Analysis.PDE.Dirichlet.quaternionForm
      (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x)).re = 0)
    (hface : CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) p q) u v)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, u x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, v x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  have hA : ContDiff ℝ 1 (fun x => OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) :=
    (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n 1).comp (contDiff_quaternionHessian_one e hψ)
  have h := quaternion_current_second_green_cell e c a b hab hA
    (fun _ => OAI.LinearAlgebra.Moore.mooreCofactor_isHermitian n _)
    (fun x j => OAI.Analysis.Calculus.Quaternion.mooreCofactor_quaternionHessian_divergence e hψ.contDiffAt j)
    hu hv hr hrne huz hnormal hface
  simpa only [OAI.LinearAlgebra.Moore.mooreCofactor_pairing n _ _ (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hv.contDiffAt),
    OAI.LinearAlgebra.Moore.mooreCofactor_pairing n _ _ (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hu.contDiffAt)] using h

theorem pencil_second_green_cell {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r u B v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B) (hv : ContDiff ℝ 2 v) (t : ℝ)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin n → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0)
    (hface : CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u v)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, u x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, v x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  apply moore_cofactor_second_green_cell e c a b hab
    (hB.add (contDiff_const.mul hu)) (hu.of_le (by norm_num)) hv hr hrne huz
    (boundary_pencil_normal_cofactor_zero e hr (hu.of_le (by norm_num))
      (hB.of_le (by norm_num)) t huz hcommon) hface

end OAI.Analysis.PDE.Green
