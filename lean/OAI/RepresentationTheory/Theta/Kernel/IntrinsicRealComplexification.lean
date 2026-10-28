import Mathlib

/-! # Intrinsic Real Complexification -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealComplexification.Intrinsic

noncomputable section

/-! Matrix complexification and extension of a real-coordinate
identity to the actual complex linear maps. -/

open scoped Classical

def complexifiedLinear {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (e : (I → ℝ) →ₗ[ℝ] (J → ℝ)) : (I → ℂ) →ₗ[ℂ] (J → ℂ) :=
  Matrix.toLin' ((LinearMap.toMatrix' e).map Complex.ofRealHom)

theorem complexifiedLinear_real {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (e : (I → ℝ) →ₗ[ℝ] (J → ℝ)) (x : I → ℝ) :
    complexifiedLinear e (fun i => (x i : ℂ)) = fun i => (e x i : ℂ) := by
  funext i
  exact (Complex.ofRealHom.map_mulVec (LinearMap.toMatrix' e) x i).symm.trans
    (congrArg (fun r : ℝ => (r : ℂ)) (congrFun (LinearMap.toMatrix'_mulVec e x) i))

theorem complexLinear_ext_real {I V : Type} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module ℂ V] (f g : (I → ℂ) →ₗ[ℂ] V)
    (h : ∀ x : I → ℝ, f (fun i => (x i : ℂ)) = g (fun i => (x i : ℂ))) : f = g := by
  apply (Pi.basisFun ℂ I).ext
  intro i
  have hc : (fun j : I => ((Pi.single i (1 : ℝ) : I → ℝ) j : ℂ)) =
      (Pi.single i (1 : ℂ) : I → ℂ) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  have he := h (Pi.single i 1)
  rw [hc] at he
  simpa only [Pi.basisFun_apply] using he

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealComplexification.Intrinsic
