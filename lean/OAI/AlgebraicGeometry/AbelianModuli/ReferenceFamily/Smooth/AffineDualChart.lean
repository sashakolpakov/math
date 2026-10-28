import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StandardSmoothChartDifferential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Localization

/-! # Affine Dual Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.AffineDualChart

noncomputable section

/-! Every smooth affine complex point has a native regular chart whose
actual derivative parametrizes all its dual-number points. -/

open scoped ContDiff

theorem exists_smoothAffine_dual_chart {S : Type*} [CommRing S] [Algebra ℂ S]
    [Algebra.Smooth ℂ S] (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) :
    ∃ (g : S) (_hg : x g ≠ 0) (n m : ℕ)
      (P : Algebra.SubmersivePresentation ℂ (Localization.Away g) (Fin n) (Fin m)),
      ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ),
        x ∈ e.source ∧
        e.source ⊆ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g ∧
        (∀ i, ∃ (a : S) (k : ℕ), ∀ y ∈ e.source, e y i = y a / (y g) ^ k) ∧
        (∀ a : S, ContDiffOn ℂ ω (fun u => e.symm u a) e.target) ∧
        ∀ u ∈ e.target, ∃ d : (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) ≃ Dual.PresentedAlgebra.DualAlgebraPoints (e.symm u),
          ∀ v a, ((d v).val a).snd = fderiv ℂ (fun w => e.symm w a) u v := by
  classical
  obtain ⟨g, hg, n, m, P, _hjac⟩ := Foundations.Scheme.SmoothComplexPoint.Algebraic.smooth_point_exists_submersive_presentation x
  let xg := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg
  obtain ⟨e0, hx0, hforward, hinverse, hdual⟩ := StandardSmoothChartDifferential.exists_standardSmooth_chart_dual_comparison P xg
  let inc := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g
  have hinc : Topology.IsOpenEmbedding inc := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction g
  let e := e0.lift_openEmbedding hinc
  have hx : x ∈ e.source := by
    change x ∈ inc '' e0.source
    exact ⟨xg, hx0, Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x g hg⟩
  have hsource : e.source ⊆ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g := by
    change inc '' e0.source ⊆ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g
    rintro y ⟨yg, _hyg, rfl⟩
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g yg).property
  have hfractions (i : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map) :
      ∃ (a : S) (k : ℕ), ∀ y ∈ e.source, e y i = y a / (y g) ^ k := by
    refine ⟨(IsLocalization.Away.sec g (P.val i.val)).1,
      (IsLocalization.Away.sec g (P.val i.val)).2, ?_⟩
    intro y hy
    change y ∈ inc '' e0.source at hy
    obtain ⟨yg, _hyg, rfl⟩ := hy
    change (e0.lift_openEmbedding hinc) (inc yg) i = _
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, hforward]
    exact ComplexPoints.Analytic.SmoothAffineCharts.localizedPoint_eval_eq_div g yg (P.val i.val)
  refine ⟨g, hg, n, m, P, e, hx, hsource, hfractions, ?_, ?_⟩
  · intro a
    change ContDiffOn ℂ ω (fun u => e0.symm u (algebraMap S (Localization.Away g) a)) e0.target
    exact hinverse _
  · intro u hu
    let d := (StandardSmoothDualCoordinates.standardSmoothDualPointsEquiv P (e0.symm u)).trans
      (Dual.Localization.dualLocalizationRestrictionEquiv g (e0.symm u))
    refine ⟨d, ?_⟩
    intro v a
    exact (congrArg TrivSqZeroExt.snd (Dual.Localization.dualLocalizationRestrictionEquiv_apply g (e0.symm u)
      (StandardSmoothDualCoordinates.standardSmoothDualPointsEquiv P (e0.symm u) v) a)).trans
        (hdual u hu v (algebraMap S (Localization.Away g) a))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.AffineDualChart
