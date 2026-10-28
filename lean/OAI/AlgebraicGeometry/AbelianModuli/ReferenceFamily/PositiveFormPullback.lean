import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.TangentMaps
import OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed

/-! # Positive Form Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveFormPullback

noncomputable section

/-! Strict positivity of actual two-forms is preserved by holomorphic
maps with injective tangent maps, including every group translation. -/

open scoped _root_.Manifold ContDiff

theorem leftTranslation_tangent_injective {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ, E) ∞ G] (g x : G) :
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : G => g * y) x) := by
  have hi : (fun y : G => g⁻¹ * y) ∘ (fun y : G => g * y) = id := by
    funext y
    exact inv_mul_cancel_left g y
  have h := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E)) x
    ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞) (a := g⁻¹)).mdifferentiableAt (by simp))
    ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞) (a := g)).mdifferentiableAt (by simp))
  rw [hi, mfderiv_id] at h
  intro u v huv
  exact (congrArg (fun A : E →L[ℝ] E => A u) h).trans
    ((congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : G => g⁻¹ * y) (g * x)) huv).trans
      (congrArg (fun A : E →L[ℝ] E => A v) h).symm)

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ, E) ∞ M] [IsManifold 𝓘(ℂ, F) ∞ N]

theorem positiveTwoForm_pullback (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N 2)
    (ha : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, F) x), v ≠ 0 →
      0 < (a x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re)
    (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g) (x : M)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x))
    (u : TangentSpace 𝓘(ℝ, E) x) (hu : u ≠ 0) :
    0 < (a.pullback g x ![u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I u]).re := by
  let D := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x
  have hDu : D u ≠ 0 := by
    intro h
    exact hu (hinj (h.trans D.map_zero.symm))
  have hv : (fun i : Fin 2 => D (![u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I u] i)) =
      ![D u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul (g x) Complex.I (D u)] := by
    funext i
    fin_cases i
    · rfl
    · exact Holomorphic.TangentMaps.holomorphicTangent_complexSMul g hg x Complex.I u
  change 0 < (a (g x) (fun i => D (![u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I u] i))).re
  rw [hv]
  exact ha (g x) (D u) hDu

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveFormPullback
