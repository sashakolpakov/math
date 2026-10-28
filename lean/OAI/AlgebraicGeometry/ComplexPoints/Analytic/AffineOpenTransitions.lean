import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOverlap

/-! # Affine Open Transitions -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenTransitions

noncomputable section

/-!
# Analytic transitions between genuine affine open charts

An overlap of actual affine open immersions is covered by principal opens.
The resulting algebra map into a localization gives explicit fractions for
every regular coordinate. Together with the analytic evaluation formulas of
the implicit-function charts, this proves compatibility across affine opens.
-/

open scoped ContDiff _root_.Topology
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- Regular-coordinate charts on two actual affine open subschemes have
complex analytic transition maps throughout their genuine overlap. -/
theorem contDiffOn_affineOpenChartTransition (A B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left] {n m : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin m → ℂ))
    (he : e ∈ SmoothSchemeManifold.affineRegularAtlas A n) (hf : f ∈ SmoothSchemeManifold.affineRegularAtlas B m) :
    ContDiffOn ℂ ω
      ((SmoothSchemeManifold.affineChartOnScheme A i e).symm.trans (SmoothSchemeManifold.affineChartOnScheme B j f))
      ((SmoothSchemeManifold.affineChartOnScheme A i e).symm.trans (SmoothSchemeManifold.affineChartOnScheme B j f)).source := by
  let T := (SmoothSchemeManifold.affineChartOnScheme A i e).symm.trans (SmoothSchemeManifold.affineChartOnScheme B j f)
  change ContDiffOn ℂ ω T T.source
  apply contDiffOn_pi.mpr
  intro k z hz
  have hez : z ∈ e.target := hz.1
  have hzimage : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z) ∈
      SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j '' f.source := hz.2
  obtain ⟨y, hy, hxy⟩ := hzimage
  obtain ⟨a, ha, h, _hfac, hpoint⟩ :=
    SchemePointHomeomorphs.schemeComplexPoints.exists_affineLocalizationTransition A B i j (e.symm z) ⟨y, hxy⟩
  let v : (Fin n → ℂ) → B → ℂ := fun w b =>
    e.symm w (IsLocalization.Away.sec a (h b)).1 /
      (e.symm w a) ^ (IsLocalization.Away.sec a (h b)).2
  have hval (w : Fin n → ℂ) (hw : e.symm w a ≠ 0) (b : B) :
      SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h ⟨e.symm w, hw⟩ b =
        v w b :=
    SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition_eval A B a h ⟨e.symm w, hw⟩ b
  have hvat (b : B) : ContDiffAt ℂ ω (fun w => v w b) z :=
    ((he.1 (IsLocalization.Away.sec a (h b)).1).contDiffAt
      (e.open_target.mem_nhds hez)).div
      (((he.1 a).contDiffAt (e.open_target.mem_nhds hez)).pow
        (IsLocalization.Away.sec a (h b)).2)
      (pow_ne_zero _ ha)
  have hqz : SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h
      ⟨e.symm z, ha⟩ = y :=
    (SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j).injective ((hpoint _).trans hxy.symm)
  obtain ⟨g, hg, hcoords⟩ := hf.2
  obtain ⟨b, r, hcoord⟩ := hcoords k
  have hgz : v z g ≠ 0 := by
    rw [← hval z ha g, hqz]
    exact hg y hy
  have hquot := (hvat b).div ((hvat g).pow r) (pow_ne_zero r hgz)
  apply ContDiffAt.contDiffWithinAt
  apply hquot.congr_of_eventuallyEq
  have hna : ∀ᶠ w in 𝓝 z, e.symm w a ≠ 0 :=
    ((he.1 a).contDiffAt (e.open_target.mem_nhds hez)).continuousAt.eventually_ne ha
  filter_upwards [T.open_source.mem_nhds hz, hna] with w hw hwa
  have hwimage : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm w) ∈
      SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j '' f.source := hw.2
  obtain ⟨yw, hyw, hxyw⟩ := hwimage
  have hqw : SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h
      ⟨e.symm w, hwa⟩ = yw :=
    (SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j).injective ((hpoint _).trans hxyw.symm)
  have hqsource : SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h
      ⟨e.symm w, hwa⟩ ∈ f.source := hqw.symm ▸ hyw
  change SmoothSchemeManifold.affineChartOnScheme B j f
      (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm w)) k = _
  rw [← hpoint ⟨e.symm w, hwa⟩, SmoothSchemeManifold.affineChartOnScheme_apply, hcoord _ hqsource,
    hval w hwa b, hval w hwa g]
  rfl

/-- Restricting scalars gives the smooth real transitions used by differential forms. -/
theorem real_contDiffOn_affineOpenChartTransition (A B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left] {n m : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin m → ℂ))
    (he : e ∈ SmoothSchemeManifold.affineRegularAtlas A n) (hf : f ∈ SmoothSchemeManifold.affineRegularAtlas B m) :
    ContDiffOn ℝ ω
      ((SmoothSchemeManifold.affineChartOnScheme A i e).symm.trans (SmoothSchemeManifold.affineChartOnScheme B j f))
      ((SmoothSchemeManifold.affineChartOnScheme A i e).symm.trans (SmoothSchemeManifold.affineChartOnScheme B j f)).source :=
  (contDiffOn_affineOpenChartTransition A B i j e f he hf).restrict_scalars ℝ

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenTransitions
