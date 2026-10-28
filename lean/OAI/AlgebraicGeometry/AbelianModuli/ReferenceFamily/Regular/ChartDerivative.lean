import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential

/-! # Chart Derivative -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.ChartDerivative

noncomputable section

/-! Actual native regular-chart transitions preserve derivatives of
regular functions and have invertible complex differential. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential Filter
open scoped ContDiff _root_.Topology

variable {S : Type*} [CommRing S] [Algebra ℂ S] {n : ℕ}

theorem regularChart_transition_bijective
    (e f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S n) (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S n)
    (u : Fin n → ℂ) (hu : u ∈ f.target) (hue : f.symm u ∈ e.source) :
    Function.Bijective (fderiv ℂ (f.symm.trans e) u) :=
  ComplexPoints.Analytic.AffineOpenDifferential.bijective_fderiv_openPartialHomeomorph (f.symm.trans e)
    ((ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas_compatible f e hf he).of_le (show (1 : ℕ∞ω) ≤ ω from le_top))
    ((ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas_compatible e f he hf).of_le (show (1 : ℕ∞ω) ≤ ω from le_top)) ⟨hu, hue⟩

theorem regularChart_transition_eval
    (e f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S n) (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S n)
    (u v : Fin n → ℂ) (hu : u ∈ f.target) (hue : f.symm u ∈ e.source) (a : S) :
    fderiv ℂ (fun w => f.symm w a) u v =
      fderiv ℂ (fun w => e.symm w a) (e (f.symm u))
        (fderiv ℂ (f.symm.trans e) u v) := by
  let t := f.symm.trans e
  have hut : u ∈ t.source := ⟨hu, hue⟩
  have ht : DifferentiableAt ℂ t u :=
    ((ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas_compatible f e hf he).contDiffAt (t.open_source.mem_nhds hut)).differentiableAt (by simp)
  have hg : DifferentiableAt ℂ (fun w => e.symm w a) (t u) :=
    ((he.1 a).contDiffAt (e.open_target.mem_nhds (e.map_source hue))).differentiableAt (by simp)
  have hd := hg.hasFDerivAt.comp u ht.hasFDerivAt
  have hc : (fun w => f.symm w a) =ᶠ[𝓝 u] (fun w => e.symm (t w) a) := by
    filter_upwards [t.open_source.mem_nhds hut] with w hw
    exact (congrArg (fun p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S => p a) (e.left_inv hw.2)).symm
  exact DFunLike.congr_fun (hd.congr_of_eventuallyEq hc).fderiv v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.ChartDerivative
