import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticElimination
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MaximalRank
import Mathlib.LinearAlgebra.Determinant

/-! # Jacobian -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.Jacobian

noncomputable section

/-! The complex Jacobian is holomorphic, and its zero locus has no
interior for a holomorphic map with finite fibers. -/

set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped _root_.Topology

variable {n : ℕ} {f : (Fin n → ℂ) → (Fin n → ℂ)} {U : Set (Fin n → ℂ)}

def holomorphicJacobian (f : (Fin n → ℂ) → (Fin n → ℂ)) (x : Fin n → ℂ) : ℂ :=
  (fderiv ℂ f x).toLinearMap.det

theorem holomorphicJacobian_ne_zero_iff (x : Fin n → ℂ) :
    holomorphicJacobian f x ≠ 0 ↔ Function.Injective (fderiv ℂ f x) := by
  simp only [holomorphicJacobian, ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot]
  rfl

theorem holomorphicJacobian_differentiableOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (holomorphicJacobian f) U := by
  have hm (i j : Fin n) : DifferentiableOn ℂ
      (fun x => (LinearMap.toMatrix' (fderiv ℂ f x).toLinearMap) i j) U := by
    have hi : DifferentiableOn ℂ (fun x => f x i) U := by
      change DifferentiableOn ℂ ((fun v : Fin n → ℂ => v i) ∘ f) U
      exact (differentiable_apply i).comp_differentiableOn hf
    have he (x : Fin n → ℂ) (hx : x ∈ U) :
        fderiv ℂ (fun z => f z i) x (Pi.single j 1) = (fderiv ℂ f x (Pi.single j 1)) i := by
      have h := ((ContinuousLinearMap.proj i).hasFDerivAt.comp x
        (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt).fderiv
      exact congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ => L (Pi.single j 1)) h
    apply (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt.Constructions.ParametricIntegral.differentiableOn_fderiv_apply hU hi (Pi.single j 1)).congr
    intro x hx
    exact (he x hx).symm
  have he : holomorphicJacobian f = fun x => (LinearMap.toMatrix' (fderiv ℂ f x).toLinearMap).det := by
    funext x
    exact (LinearMap.det_toMatrix' _).symm
  rw [he]
  simp only [Matrix.det_apply']
  apply DifferentiableOn.fun_sum
  intro σ _
  exact (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticElimination.Constructions.Elimination.differentiableOn_finset_product Finset.univ (fun i _ => hm (σ i) i)).const_mul _

theorem holomorphicJacobian_not_eventually_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hfinite : ∀ y, {z | z ∈ U ∧ f z = y}.Finite) {x : Fin n → ℂ} (hx : x ∈ U) :
    ¬∀ᶠ y in 𝓝 x, holomorphicJacobian f y = 0 := by
  intro hzero
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) hzero)
  have hsub : V ⊆ U := fun _ hz => (hVU hz).1
  obtain ⟨z, hz, hzinj⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MaximalRank.Constructions.FiniteRank.exists_injective_fderiv_of_finite_fibers hV ⟨x, hxV⟩
    (hf.mono hsub) (fun y => (hfinite y).subset (fun _ hw => ⟨hsub hw.1, hw.2⟩))
  exact (holomorphicJacobian_ne_zero_iff z).mpr hzinj (hVU hz).2

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.Jacobian
