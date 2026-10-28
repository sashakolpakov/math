import OAI.RepresentationTheory.Theta.Geometric.Torus.PolarizationCurvature
import OAI.Analysis.DifferentialForms.Manifold.Holomorphic
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ManifoldMetric

/-! # Period Curvature Invariance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodCurvatureInvariance

noncomputable section

/-! The original constant polarization curvature is invariant under
actual translations of the period torus, including their tangent maps. -/

open OAI.Analysis.DifferentialForms.Manifold.Holomorphic
open scoped _root_.Manifold ContDiff

variable (Φ : RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData)

theorem periodTranslation_chart_fderiv (t i j : Φ.periodTorus) (w : Φ.space)
    (hw : t + (Φ.periodChart i).symm w ∈ (Φ.periodChart j).source) :
    fderiv ℝ (Φ.periodChart j ∘ (fun q => t + q) ∘ (Φ.periodChart i).symm) w =
      ContinuousLinearMap.id ℝ Φ.space := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective t
  have ha : (QuotientAddGroup.mk (a + w) : Φ.periodTorus) ∈ (Φ.periodChart j).source := by
    simpa only [Φ.periodChart_symm, QuotientAddGroup.mk_add] using hw
  have hd := (Φ.periodSection_hasFDerivAt (Φ.periodChart j) (Φ.periodChart_symm j) (a + w) ha).comp w
    ((hasFDerivAt_id w).const_add a)
  have he : Φ.periodChart j ∘ (fun q => (QuotientAddGroup.mk a : Φ.periodTorus) + q) ∘
      (Φ.periodChart i).symm = fun y => Φ.periodChart j (QuotientAddGroup.mk (a + y)) := by
    funext y
    simp only [Function.comp_apply, Φ.periodChart_symm, QuotientAddGroup.mk_add]
  rw [he]
  exact hd.fderiv

theorem periodTranslation_contMDiff (t : Φ.periodTorus) :
    ContMDiff 𝓘(ℝ, Φ.space) 𝓘(ℝ, Φ.space) ∞ (fun q : Φ.periodTorus => t + q) :=
  Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (contMDiff_const.add contMDiff_id)

theorem periodCurvature_translation (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ) (t : Φ.periodTorus) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun q : Φ.periodTorus => t + q) (periodTranslation_contMDiff Φ t)
      (Φ.torusCurvature H) = Φ.torusCurvature H := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro q
  let c := Φ.periodChart q
  let d := Φ.periodChart (t + q)
  have hc : c ∈ atlas Φ.space Φ.periodTorus := Φ.periodChart_mem_atlas q
  have hd : d ∈ atlas Φ.space Φ.periodTorus := Φ.periodChart_mem_atlas (t + q)
  have hq : q ∈ c.source := Φ.mem_periodChart_source q
  have ht : t + c.symm (c q) ∈ d.source := by
    rw [c.left_inv hq]
    exact Φ.mem_periodChart_source (t + q)
  apply ComplexMultiplication.HodgeComparison.ManifoldMetric.CM.Construction.rawManifoldForm_eq_at_of_inChart_eq _ _ c hc q hq
  have hp := (Φ.torusCurvature H).val.pullback_inChart (fun x : Φ.periodTorus => t + x)
    c d hc hd (c.map_source hq) ht ((periodTranslation_contMDiff Φ t).mdifferentiableAt (by simp))
  refine hp.trans ?_
  have hv := Φ.torusCurvatureRaw_inChart H (t + q) (d (t + c.symm (c q))) (d.map_source ht)
  have hD := periodTranslation_chart_fderiv Φ t q (t + q) (c q) ht
  change ((Φ.torusCurvatureRaw H).inChart d (d (t + c.symm (c q)))).compContinuousLinearMap
    (fderiv ℝ (d ∘ (fun x => t + x) ∘ c.symm) (c q)) = (Φ.torusCurvatureRaw H).inChart c (c q)
  rw [hv, hD, Φ.torusCurvatureRaw_inChart H q (c q) (c.map_source hq)]
  ext v
  change RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature H (d (t + c.symm (c q))) v = RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature H (c q) v
  rw [RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature_apply, RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodCurvatureInvariance
