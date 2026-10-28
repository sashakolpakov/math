import OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed

/-! # Invariant Pullback Chart -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.InvariantPullbackChart

noncomputable section

/-! # Actual chart formula for pullback of invariant manifold forms -/

open scoped ContDiff _root_.Manifold

open OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology

variable {E F M G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Group G] [TopologicalSpace G] [ChartedSpace F G] [LieGroup 𝓘(ℝ, F) ∞ G]

/-- The coordinate formula uses the derivative of the actual translated source map. -/
theorem invariantRawForm_pullback_inChart (n : ℕ)
    (α : TangentSpace 𝓘(ℝ, F) (1 : G) [⋀^Fin n]→L[ℝ] ℂ)
    (f : M → G) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph G F)
    (hc : c ∈ atlas E M) (hd : d ∈ atlas F G)
    (h1 : (1 : G) ∈ d.source) {y : E} (hy : y ∈ c.target) :
    ((AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantRawForm α).pullback f).inChart c y =
      (α.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap d (d 1))).compContinuousLinearMap
        (fderiv ℝ (fun w => d ((f (c.symm y))⁻¹ * f (c.symm w))) y) := by
  let β : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F G n := fun _ => α
  let k : M → G := fun x => (f (c.symm y))⁻¹ * f x
  have hk : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ k :=
    (contMDiff_mul_left (I := 𝓘(ℝ, F)) (n := ∞)).comp hf
  have hpoint : k (c.symm y) = 1 := inv_mul_cancel _
  have hp := β.pullback_inChart k c d hc hd hy
    (by rw [hpoint]; exact h1) (hk.mdifferentiableAt (by simp))
  rw [hpoint] at hp
  have hder := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))
    (I'' := 𝓘(ℝ, F)) (c.symm y)
    ((contMDiff_mul_left (I := 𝓘(ℝ, F)) (n := ∞)
      (a := (f (c.symm y))⁻¹)).mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  calc
    ((AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantRawForm α).pullback f).inChart c y = (β.pullback k).inChart c y := by
      apply ContinuousAlternatingMap.ext
      intro v
      change α (fun i =>
        mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun g : G => (f (c.symm y))⁻¹ * g) (f (c.symm y))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c.symm y)
            (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap c y (v i)))) =
        α (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) k (c.symm y)
          (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap c y (v i)))
      apply congrArg α
      funext i
      exact (congrArg (fun linear => linear (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap c y (v i))) hder).symm
    _ = _ := by
      simpa only [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart, Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap, β, k,
        Function.comp_def] using! hp

end

end OAI.AlgebraicGeometry.ComplexMultiplication.InvariantPullbackChart
