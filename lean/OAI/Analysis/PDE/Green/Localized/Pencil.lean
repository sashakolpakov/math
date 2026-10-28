import OAI.Analysis.PDE.Green.Localized.Boundary
import OAI.Analysis.PDE.Green.CellPencil

/-! The determinant-pencil identity with boundary assumptions localized to
the support of the time test. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Topology Matrix.Norms.Elementwise MatrixOrder ComplexOrder

theorem quaternion_current_second_green_localized {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hAh : ∀ x, (A x).IsHermitian)
    (hdiv : ∀ x j, OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0)
    {r u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hreg : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ v =ᶠ[𝓝 x] (fun _ => 0))
    (hzero : ∀ x, r x = 0 → ∑ p, fderiv ℝ r x (OAI.Analysis.PDE.Dirichlet.coordinateVector p) *
      secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) u v p x = 0)
    (hface : CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) u v)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      v x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  have hK (p q : Fin n × Fin s) : ContDiff ℝ 1 (fun x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) :=
    (realCoefficientCLM e p q).contDiff.comp hA
  have hKs (p q : Fin n × Fin s) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q = OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) q p :=
    (congrFun (congrFun (OAI.Analysis.Calculus.Quaternion.realCoefficients_isSymm e (A x) (hAh x)) p) q).symm
  have hd (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (q : Fin n × Fin s) :
      (∑ p, fderiv ℝ (fun y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) = 0 := by
    simp_rw [fderiv_realCoefficient e _ _ (hA.differentiable (by norm_num) x)]
    exact OAI.Analysis.Calculus.Quaternion.realCoefficients_divergence_zero e _ (hdiv x) q
  have h := real_operator_second_green_cell_localized c a b hab
    (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) hK hu hv hr hKs hd hreg hzero hface
  have hform (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hf : ContDiff ℝ 2 f) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x) =
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q * OAI.Analysis.PDE.Dirichlet.realHessian f x p q :=
    realTrace_hessianMap (A x) e (OAI.Analysis.PDE.Dirichlet.realHessian f x) (OAI.Analysis.PDE.Dirichlet.realHessian_isSymm hf.contDiffAt)
  simpa only [hform u hu, hform v hv, OAI.Analysis.PDE.Dirichlet.realHessian, OAI.Analysis.PDE.Dirichlet.coordinateVector] using h

theorem moore_cofactor_second_green_localized {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {ψ r u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hreg : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ v =ᶠ[𝓝 x] (fun _ => 0))
    (hzero : ∀ x, r x = 0 → ∑ p, fderiv ℝ r x (OAI.Analysis.PDE.Dirichlet.coordinateVector p) *
      secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
        (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ y)) p q) u v p x = 0)
    (hface : CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) p q) u v)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, u x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, v x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  have hA : ContDiff ℝ 1 (fun x => OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) :=
    (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n 1).comp (contDiff_quaternionHessian_one e hψ)
  have h := quaternion_current_second_green_localized e c a b hab hA
    (fun _ => OAI.LinearAlgebra.Moore.mooreCofactor_isHermitian n _)
    (fun x j => OAI.Analysis.Calculus.Quaternion.mooreCofactor_quaternionHessian_divergence e hψ.contDiffAt j)
    hu hv hr hreg hzero hface
  simpa only [OAI.LinearAlgebra.Moore.mooreCofactor_pairing n _ _ (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hv.contDiffAt),
    OAI.LinearAlgebra.Moore.mooreCofactor_pairing n _ _ (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hu.contDiffAt)] using h

theorem pencil_second_green_localized {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r u B v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B) (hv : ContDiff ℝ 2 v) (t : ℝ)
    (hreg : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ v =ᶠ[𝓝 x] (fun _ => 0))
    (hboundary : ∀ x, r x = 0 →
      ((∀ᶠ y in 𝓝 x, r y = 0 → u y = 0) ∧
        ∃ w : Fin n → Quaternion ℝ, w ≠ 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧
          OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧ star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0) ∨
      v =ᶠ[𝓝 x] (fun _ => 0))
    (hface : CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u v)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, u x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, v x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  apply moore_cofactor_second_green_localized e c a b hab
    (hB.add (contDiff_const.mul hu)) (hu.of_le (by norm_num)) hv hr hreg _ hface
  intro x hx
  rcases hboundary x hx with ⟨hz, hc⟩ | hz
  · apply secondGreenFlux_tangent_local OAI.Analysis.PDE.Dirichlet.coordinateVector _ hr (hu.of_le (by norm_num)) x hx hz
    rw [realCoefficients_quadratic]
    exact boundary_pencil_normal_cofactor_zero_local e hr (hu.of_le (by norm_num))
      (hB.of_le (by norm_num)) t x hx hz hc
  · have hf := (secondGreenFlux_eventually_zero OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u v x hz).self_of_nhds
    simp only [hf, mul_zero, Finset.sum_const_zero]

theorem determinant_pencil_variation_localized {n s m : ℕ}
    (e : Fin s → Quaternion ℝ) (c : (Fin n × Fin s) ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r u B v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B) (hv : ContDiff ℝ 3 v)
    (hreg : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ v =ᶠ[𝓝 x] (fun _ => 0))
    (hboundary : ∀ x, r x = 0 →
      ((∀ᶠ y in 𝓝 x, r y = 0 → u y = 0) ∧
        ∃ w : Fin n → Quaternion ℝ, w ≠ 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧
          OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧ star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0) ∨
      v =ᶠ[𝓝 x] (fun _ => 0))
    (hface : ∀ t : ℝ, CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u v)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∫ t in (0 : ℝ)..1, u x * OAI.LinearAlgebra.Moore.mooreDifferential n
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, v x *
      (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) -
        OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
  have hb := (isBounded_euclidean_cell c a b).subset
    (inter_subset_left : ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) ⊆ _)
  have hgreen (t : ℝ) := pencil_second_green_localized e c a b hab hr hu hB
    (hv.of_le (by norm_num)) t hreg hboundary (hface t)
  simp_rw [quaternionHessian_add_mul e (hB.of_le (by norm_num))
    (hu.of_le (by norm_num))] at hgreen ⊢
  have he := integrate_pencil_green hb hu.continuous hv.continuous
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hB)
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hu)
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hv) hgreen
  simpa only [OAI.Analysis.PDE.Energy.hessian_sum e (hB.of_le (by norm_num))
    (hu.of_le (by norm_num))] using he

end OAI.Analysis.PDE.Green
