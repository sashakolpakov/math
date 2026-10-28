import OAI.Analysis.DifferentialForms.Manifold.PurePullback

/-! # Tangent Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.TangentMaps

noncomputable section

/-! Holomorphic maps intertwine the actual complex actions on the real
tangent spaces, through their genuine chart differentials. -/

open OAI.Analysis.DifferentialForms.Manifold.PurePullback
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem preferredTangent_identity {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) (v : E) :
    Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x v = v := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) x v = v
  rw [mfderiv_extChartAt_self]
  rfl

theorem preferredTangent_inverse_identity {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) (v : E) :
    (Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x).symm v = v := by
  apply (Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x).injective
  exact (ContinuousLinearEquiv.apply_symm_apply _ v).trans (preferredTangent_identity x v).symm

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ, E) ∞ M] [IsManifold 𝓘(ℂ, F) ∞ N]

theorem complexTangentSMul_model (x : M) (z : ℂ) (u : E) :
    Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x z u = z • u := by
  have h (v : E) : Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x v = v := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) x v = v
    rw [mfderiv_extChartAt_self]
    rfl
  have hi (v : E) : (Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x).symm v = v := by
    apply (Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x).injective
    exact (ContinuousLinearEquiv.apply_symm_apply _ v).trans (h v).symm
  exact (hi (z • Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x u)).trans (congrArg (fun v => z • v) (h u))

theorem holomorphicTangent_chart (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ atlas E M) (hf : f ∈ atlas F N) (x : M)
    (hex : x ∈ e.source) (hfx : g x ∈ f.source) :
    (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap f (g x)).comp
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x).comp (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap e (e x))) =
      (fderiv ℂ (f ∘ g ∘ e.symm) (e x)).restrictScalars ℝ := by
  have hy : g (e.symm (e x)) ∈ f.source := by rwa [e.left_inv hex]
  have hr := Analysis.DifferentialForms.Manifold.ManifoldPullback.fderiv_manifoldMap_inChart g e f he hf (e.map_source hex) hy
    ((Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg).mdifferentiableAt (by simp))
  have hc := (Analysis.DifferentialForms.Manifold.Holomorphic.complexContDiffAt_manifoldMap_inChart g e f he hf (e.map_source hex) hy
    hg.contMDiffAt).differentiableAt (by simp)
  rw [e.left_inv hex] at hr
  exact hr.symm.trans (hc.fderiv_restrictScalars ℝ)

theorem holomorphicTangent_complexSMul (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)
    (x : M) (z : ℂ) (u : TangentSpace 𝓘(ℝ, E) x) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x z u) =
      Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul (g x) z (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x u) := by
  let e := chartAt E x
  let f := chartAt F (g x)
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hf : f ∈ atlas F N := chart_mem_atlas F (g x)
  have hex : x ∈ e.source := mem_chart_source E x
  have hfx : g x ∈ f.source := mem_chart_source F (g x)
  let D := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x
  let T := fderiv ℂ (f ∘ g ∘ e.symm) (e x)
  have hD (w : E) : Analysis.DifferentialForms.Manifold.Charts.chartTangentMap f (g x) (D (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap e (e x) w)) = T w :=
    congrArg (fun A : E →L[ℝ] F => A w) (holomorphicTangent_chart g hg e f he hf x hex hfx)
  have hinv : Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap e (e x) (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x u) = u :=
    (Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hex).symm_apply_apply u
  apply (Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv f hf (g x) hfx).injective
  change Analysis.DifferentialForms.Manifold.Charts.chartTangentMap f (g x) (D (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x z u)) =
    Analysis.DifferentialForms.Manifold.Charts.chartTangentMap f (g x) (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul (g x) z (D u))
  rw [Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul_inChart f hf (g x) hfx]
  calc
    _ = T (z • Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x u) := hD _
    _ = z • T (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x u) := T.map_smul z _
    _ = z • Analysis.DifferentialForms.Manifold.Charts.chartTangentMap f (g x) (D u) :=
      congrArg (fun w => z • w) ((hD _).symm.trans (congrArg (fun w => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap f (g x) (D w)) hinv))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.TangentMaps
