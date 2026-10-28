import OAI.Analysis.PDE.Dirichlet.SchauderIsometryEquation
import OAI.Analysis.PDE.Dirichlet.C2HolderCoefficient
import OAI.Analysis.PDE.Dirichlet.Derivative

noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem directional_isometry_comp {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ) (hu : Differentiable ℝ u) (v : E) :
    OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ e) v = (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (e v)) ∘ e := by
  funext x
  exact OAI.Analysis.PDE.Dirichlet.fderiv_isometry_comp e u hu x v

/-- The differentiated nonlinear equation in ordinary Euclidean coordinates.
Both the real coefficient and the directional forcing are the actual
derivatives of the Moore equation, not independent input identities. -/
theorem moore_directional_equation_isometry [FiniteDimensional ℝ E] {n : ℕ}
    (e : E ≃ₗᵢ[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hu : ContDiff ℝ 3 u) (x v : E) (hf : DifferentiableAt ℝ f (e x))
    (heq : (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 (e x)] f) :
    OAI.Analysis.PDE.Elliptic.ellipticTrace
      (fun y => OAI.Analysis.PDE.Dirichlet.isometryConjugate e (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (e y))))
      (OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ e) v) x = OAI.Analysis.PDE.Dirichlet.directionalDerivative f (e v) (e x) := by
  rw [directional_isometry_comp e u (hu.differentiable (by norm_num)) v,
    OAI.Analysis.PDE.Dirichlet.ellipticTrace_isometry_pullback e (fun y => OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      _ (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) (e v)),
    OAI.Analysis.PDE.Dirichlet.detRealOperator_linearization _ (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) (e v))]
  exact OAI.Analysis.PDE.Dirichlet.mooreLinearization_directional_eq hu (e v) hf heq

theorem moore_directional_equation_isometry_on_open [FiniteDimensional ℝ E] {n : ℕ}
    (e : E ≃ₗᵢ[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hu : ContDiff ℝ 3 u) {Ω : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℝ f Ω)
    (heq : ∀ y ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y) = f y)
    (x v : E) (hx : e x ∈ Ω) :
    OAI.Analysis.PDE.Elliptic.ellipticTrace
      (fun y => OAI.Analysis.PDE.Dirichlet.isometryConjugate e (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (e y))))
      (OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ e) v) x = OAI.Analysis.PDE.Dirichlet.directionalDerivative f (e v) (e x) := by
  apply moore_directional_equation_isometry e u f hu x v
    ((hf (e x) hx).differentiableAt (hΩ.mem_nhds hx))
  filter_upwards [hΩ.mem_nhds hx] with y hy
  exact heq y hy

/-- Uniform Hölder control of the true Moore coefficient uses only the
original C²,α jet bound. It does not use any third derivative bound. -/
theorem exists_actual_moore_coefficient_bound {n : ℕ}
    {Ω K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} {hΩK : Ω ⊆ K} {α R : ℝ}
    (hα : 0 ≤ α) (hR : 0 ≤ R) :
    ∃ N ≥ 0, ∀ (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α),
      ‖U‖ ≤ R →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ x ∈ K, ‖OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)‖ ≤ N) ∧
      (∀ x ∈ K, ∀ y ∈ K,
        ‖OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)-
          OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)‖ ≤ N*dist x y^α) := by
  obtain ⟨N,hN,hcoef⟩ := OAI.Analysis.PDE.Dirichlet.exists_detRealCoefficient_bound (hΩK := hΩK) hα hR
  refine ⟨N,hN,?_⟩
  intro u U hUn hU₂
  obtain ⟨a,ha,han⟩ := hcoef U hUn
  have hactual (x : K) : OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) := by
    rw [ha]
    congr 1
    change OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j => OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x
      (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)) = _
    rw [hU₂]
    rfl
  constructor
  · intro x hx
    rw [← hactual ⟨x,hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le a ⟨x,hx⟩).trans han
  · intro x hx y hy
    rw [← hactual ⟨x,hx⟩, ← hactual ⟨y,hy⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le a ⟨x,hx⟩ ⟨y,hy⟩).trans
      (mul_le_mul_of_nonneg_right han (Real.rpow_nonneg dist_nonneg _))

end OAI.Analysis.PDE.Schauder
