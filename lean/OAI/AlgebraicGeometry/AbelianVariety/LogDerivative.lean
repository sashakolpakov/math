import OAI.AlgebraicGeometry.AbelianVariety.AveragingDerivative
import OAI.AlgebraicTopology.DeRham.Comparison.NormedManifoldPullback

/-! # Log Derivative -/

namespace OAI.AlgebraicGeometry.AbelianVariety.LogDerivative.Constructions.ExteriorCohomology

noncomputable section

/-!
# Smooth translation coefficients of pullbacks for ExteriorCohomology

A smooth map into a Lie group has a smooth left logarithmic derivative.
This identifies translated pullbacks with smooth invariant-frame coefficients
and proves the joint continuity needed for period averaging.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E G V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G]

def leftLogDerivative (σ : V → G) (t : V) : V →L[ℝ] E :=
  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => (σ t)⁻¹ * h) (σ t)).comp
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) σ t)

theorem leftLogDerivative_inChart (σ : V → G) (hσ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ σ)
    (d : OpenPartialHomeomorph G E) (hd : d ∈ atlas E G) (h1 : (1 : G) ∈ d.source) (t : V) :
    leftLogDerivative (E := E) (G := G) σ t = (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap d (d 1)).comp
      (fderiv ℝ (fun w => d ((σ t)⁻¹ * σ w)) t) := by
  have hi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => (σ t)⁻¹ * h) (σ t) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp)
  have hs := hσ.mdifferentiableAt (x := t) (by simp)
  have hm := mfderiv_comp (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E)) t hi hs
  have hc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) d ((σ t)⁻¹ * σ t) := by
    rw [inv_mul_cancel]
    exact mdifferentiableAt_atlas hd h1
  have hdt := mfderiv_comp (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
    t hc (hi.comp t hs)
  rw [mfderiv_eq_fderiv, hm] at hdt
  simp only [Function.comp_apply] at hdt
  rw [inv_mul_cancel] at hdt
  change fderiv ℝ (fun w => d ((σ t)⁻¹ * σ w)) t =
    (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap d 1).comp (leftLogDerivative (E := E) (G := G) σ t) at hdt
  rw [hdt]
  ext v
  change leftLogDerivative (E := E) (G := G) σ t v =
    Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap d (d 1) (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap d 1 (leftLogDerivative (E := E) (G := G) σ t v))
  exact (congrArg (fun L : E →L[ℝ] E => L (leftLogDerivative (E := E) (G := G) σ t v))
    (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap_comp d hd h1)).symm

theorem leftLogDerivative_contDiff (σ : V → G)
    (hσ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ σ) : ContDiff ℝ ∞ (leftLogDerivative (E := E) (G := G) σ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  let d := chartAt E (1 : G)
  have hd : d ∈ atlas E G := chart_mem_atlas E (1 : G)
  have h1 : (1 : G) ∈ d.source := mem_chart_source E (1 : G)
  have hm : ContMDiffAt 𝓘(ℝ, V × V) 𝓘(ℝ, E) ∞
      (fun p : V × V => (σ p.1)⁻¹ * σ p.2) (t, t) :=
    ((hσ.contMDiffAt.comp (t, t) contDiffAt_fst.contMDiffAt).inv).mul
      (hσ.contMDiffAt.comp (t, t) contDiffAt_snd.contMDiffAt)
  have hd' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ d ((σ t)⁻¹ * σ t) := by
    rw [inv_mul_cancel]
    exact contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd) h1
  have ht : ContDiffAt ℝ ∞ (fun p : V × V => d ((σ p.1)⁻¹ * σ p.2)) (t, t) :=
    (hd'.comp (t, t) hm).contDiffAt
  have hder : ContDiffAt ℝ ∞ (fun z => fderiv ℝ (fun w => d ((σ z)⁻¹ * σ w)) z) t :=
    ht.fderiv contDiffAt_id (by simp)
  let L : E →L[ℝ] E := Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap d (d 1)
  have hL : ContDiffAt ℝ ∞ (fun _ : V => L) t := contDiffAt_const
  apply (hL.clm_comp hder).congr_of_eventuallyEq
  exact Eventually.of_forall (leftLogDerivative_inChart σ hσ d hd h1)

variable {n : ℕ}

def translatedPullbackValue (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (σ : V → G) (g : G) (t : V) :
    V [⋀^Fin n]→L[ℝ] ℂ :=
  (((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).pullback (E := E) (fun h : G => g * h)).pullback
    (E := V) σ).toNormedSpace t

theorem translatedPullbackValue_eq_coefficient (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (σ : V → G) (g : G) (t : V) :
    translatedPullbackValue form σ g t =
      (Averaging.Constructions.ExteriorCohomology.leftCoefficient form (g * σ t)).compContinuousLinearMap
        (leftLogDerivative (E := E) (G := G) σ t) := by
  change ((AveragingDerivative.Constructions.ExteriorCohomology.translatedValue form g (σ t)).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) σ t)).compContinuousLinearMap
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm.toContinuousLinearMap = _
  rw [AveragingDerivative.Constructions.ExteriorCohomology.translatedValue_eq_coefficient]
  ext v
  rfl

theorem translatedPullbackValue_continuous (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (σ : V → G) (hσ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ σ) :
    Continuous (fun p : G × V => translatedPullbackValue form σ p.1 p.2) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ, E)) (n := ∞)
  have hc : Continuous (fun p : G × V => Averaging.Constructions.ExteriorCohomology.leftCoefficient form (p.1 * σ p.2)) :=
    (Averaging.Constructions.ExteriorCohomology.leftCoefficient_contMDiff form).continuous.comp
      (continuous_fst.mul (hσ.continuous.comp continuous_snd))
  have hl : Continuous (fun p : G × V => leftLogDerivative (E := E) (G := G) σ p.2) :=
    (leftLogDerivative_contDiff σ hσ).continuous.comp continuous_snd
  have hL := ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM
    (ι := Fin n) (𝕜 := ℝ) (G := ℂ) |>.comp hl
  exact (hL.clm_apply hc).congr (fun p =>
    (translatedPullbackValue_eq_coefficient form σ p.1 p.2).symm)

end

end OAI.AlgebraicGeometry.AbelianVariety.LogDerivative.Constructions.ExteriorCohomology
