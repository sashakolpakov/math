import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BerryLogarithmicDescent

/-! # Local Berry Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalBerryPullback.CM.Construction

noncomputable section

/-! The ambient local connection agrees with the connection obtained
by restricting the homogeneous lift to the intrinsic open manifold. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {ι : Type} [Fintype ι]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem intrinsicLift_contMDiff (U : Opens M) (f : M → ι → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ f U) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ (fun x : U => f x.val) :=
  hf.comp_contMDiff (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (n := ∞)) (fun x => x.property)

def localLiftBerry (U : Opens M) (f : M → ι → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ f U) (hn : ∀ x ∈ U, f x ≠ 0) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ofRaw U (ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) f)
    (ManifoldMetric.CM.Construction.manifoldLiftBerry_smooth U.isOpen f hf hn)

theorem localLiftBerry_intrinsic (U : Opens M) (f : M → ι → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ f U) (hn : ∀ x ∈ U, f x ≠ 0) :
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U 1 (localLiftBerry U f hf hn) =
      BerryLogarithmicDescent.CM.Construction.smoothLiftBerry (fun x : U => f x.val) (intrinsicLift_contMDiff U f hf)
        (fun x => hn x.val x.property) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  change ManifoldMetric.CM.Construction.homogeneousManifoldBerry (f x.val)
    (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ι → ℂ) f x.val
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x (v i))) =
    ManifoldMetric.CM.Construction.homogeneousManifoldBerry (f x.val)
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ι → ℂ) (fun y : U => f y.val) x (v i))
  apply congrArg (ManifoldMetric.CM.Construction.homogeneousManifoldBerry (f x.val))
  funext i
  have hF := ((ManifoldMetric.CM.Construction.manifoldLift_realSmooth U.isOpen f hf x.val x.property).contMDiffAt
    (U.isOpen.mem_nhds x.property)).mdifferentiableAt (by simp)
  have hinc := (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞)).mdifferentiableAt
    (x := x) (by simp)
  exact (congrArg (fun L => L (v i)) (mfderiv_comp x hF hinc)).symm

theorem localLiftBerry_restrict {U W : Opens M} (hWU : W ≤ U) (f : M → ι → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ f U) (hn : ∀ x ∈ U, f x ≠ 0) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hWU (localLiftBerry U f hf hn) =
      localLiftBerry W f (hf.mono hWU) (fun x hx => hn x (hWU hx)) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalBerryPullback.CM.Construction
