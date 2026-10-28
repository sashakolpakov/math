import OAI.Geometry.Nikodym.Riemannian.Smooth
import OAI.Geometry.Nikodym.OpenMFDeriv
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap

noncomputable section
open Set Bundle Manifold _root_.MeasureTheory
open scoped ContDiff ENNReal NNReal

namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The genuine straight-line path in a convex open coordinate domain. -/
def opensSegment (U : TopologicalSpace.Opens E) (hc : Convex ℝ (U : Set E))
    (x y : U) : Path x y where
  toFun t := ⟨AffineMap.lineMap (x : E) (y : E) (t : ℝ),
    hc.lineMap_mem x.property y.property t.property⟩
  continuous_toFun := by continuity
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

omit [FiniteDimensional ℝ E] in
theorem contMDiff_opensSegment (U : TopologicalSpace.Opens E)
    (hc : Convex ℝ (U : Set E)) (x y : U) :
    CMDiff ∞ (opensSegment U hc x y) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  change ContMDiff (𝓡∂ 1) 𝓘(ℝ,E) ∞ (AffineMap.lineMap (x : E) (y : E) ∘
    (Subtype.val : unitInterval → ℝ))
  have hline : ContDiff ℝ ∞ (AffineMap.lineMap (x : E) (y : E) : ℝ → E) := by fun_prop
  exact hline.contMDiff.comp contMDiff_subtypeVal_Icc

omit [FiniteDimensional ℝ E] in
theorem mfderiv_opensSegment_one (U : TopologicalSpace.Opens E)
    (hc : Convex ℝ (U : Set E)) (x y : U) (t : unitInterval) :
    (mfderiv% (opensSegment U hc x y) t 1 : E) = (y : E) - (x : E) := by
  let γ := opensSegment U hc x y
  have hγ : CMDiff ∞ γ := contMDiff_opensSegment U hc x y
  have hincl := mfderiv_comp_apply t
    (opens_mdifferentiable_subtype_val U (γ t))
    ((hγ.mdifferentiable (by norm_num)) t) 1
  rw [opens_mfderiv_subtype_val] at hincl
  change mfderiv (𝓡∂ 1) 𝓘(ℝ,E)
    (AffineMap.lineMap (x : E) (y : E) ∘ (Subtype.val : unitInterval → ℝ)) t 1 = _ at hincl
  have hline : HasDerivAt (AffineMap.lineMap (x : E) (y : E) : ℝ → E)
      ((y : E) - (x : E)) (t : ℝ) := AffineMap.hasDerivAt_lineMap
  have htime : MDifferentiable (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) :=
    (contMDiff_subtypeVal_Icc (n := 1)).mdifferentiable one_ne_zero
  rw [mfderiv_comp_apply t hline.differentiableAt.mdifferentiableAt (htime t),
    mfderiv_subtypeVal_Icc_one, mfderiv_eq_fderiv] at hincl
  rw [hline.hasFDerivAt.fderiv] at hincl
  change (1 : ℝ) • ((y : E) - (x : E)) = (mfderiv% γ t 1 : E) at hincl
  simpa only [one_smul] using! hincl.symm

namespace SmoothCoordinateMetric

attribute [local instance] Measure.Subtype.measureSpace

/-- A uniform upper quadratic-form bound bounds intrinsic distance on a convex domain. -/
theorem riemannianEDist_le_of_convex (g : SmoothCoordinateMetric E)
    (hc : Convex ℝ g.domain) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z ∈ g.domain, ∀ v : E, g.inner z v v ≤ C * ‖v‖ ^ 2) :
    letI := g.toRiemannianBundle
    ∀ x y : g.openDomain,
      riemannianEDist 𝓘(ℝ,E) x y ≤
        ENNReal.ofReal (Real.sqrt C) * edist (x : E) (y : E) := by
  let := g.toRiemannianBundle
  intro x y
  let γ := opensSegment g.openDomain hc x y
  have hγ : CMDiff 1 γ := (contMDiff_opensSegment g.openDomain hc x y).of_le (by norm_num)
  have hle : riemannianEDist 𝓘(ℝ,E) x y ≤ ∫⁻ t, ‖mfderiv% γ t 1‖ₑ := by
    rw [riemannianEDist]
    exact biInf_le _ hγ
  have hv (t : unitInterval) :
      ‖mfderiv% γ t 1‖ ≤ Real.sqrt C * ‖(y : E) - x‖ := by
    rw [norm_eq_sqrt_real_inner]
    change Real.sqrt (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1)) ≤ _
    have heq : (mfderiv% γ t 1 : E) = (y : E) - (x : E) :=
      mfderiv_opensSegment_one g.openDomain hc x y t
    have hinner : g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1) =
        g.inner (γ t) ((y : E) - x) ((y : E) - x) := by
      exact congrArg (fun v : E => g.inner (γ t) v v) heq
    rw [hinner]
    calc
      Real.sqrt (g.inner (γ t) ((y : E) - x) ((y : E) - x)) ≤
          Real.sqrt (C * ‖(y : E) - x‖ ^ 2) := Real.sqrt_le_sqrt
            (hbound (γ t) (γ t).property _)
      _ = Real.sqrt C * ‖(y : E) - x‖ := by
        rw [Real.sqrt_mul hC.le, Real.sqrt_sq (norm_nonneg _)]
  calc
    riemannianEDist 𝓘(ℝ,E) x y ≤ ∫⁻ t, ‖mfderiv% γ t 1‖ₑ := hle
    _ ≤ ∫⁻ _t : unitInterval, ENNReal.ofReal (Real.sqrt C * ‖(y : E) - x‖) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hv t)
    _ = ENNReal.ofReal (Real.sqrt C) * edist (x : E) (y : E) := by
      simp only [lintegral_const, measure_univ, mul_one]
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), edist_eq_enorm_sub,
        ← ofReal_norm, norm_sub_rev]

end SmoothCoordinateMetric
end OAI.Geometry.Nikodym
