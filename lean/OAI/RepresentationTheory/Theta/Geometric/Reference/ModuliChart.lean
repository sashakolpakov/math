import OAI.RepresentationTheory.Theta.Geometric.Family.IntrinsicChart
import OAI.RepresentationTheory.Theta.Geometric.Local.ReferenceModuliPeriods
import OAI.RepresentationTheory.Theta.Geometric.Universal.HolomorphicTransport

/-! # Moduli Chart -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! At an actual reference point of a two-dimensional original moduli
subspace, the exact reference period is a holomorphic local chart. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ D.pel.complexSpace) [Mono f]

theorem Data.ActiveHeckeThetaData.exists_reference_moduli_chart (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hdim : AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (a : D.domain) (ha : x ≫ f = D.referenceModuliMap hg a) :
    ∃ e : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) Geometry.ComplexBall.PrescribedSignsB.BallChart,
      x ∈ e.source ∧ e x = a.val ∧
      e.MDifferentiable (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ))
        (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart)) ∧
      e.target ⊆ D.domain ∧
      ∀ y ∈ e.source, ∃ hp : e y ∈ D.domain,
        y ≫ f = D.referenceModuliMap hg ⟨e y, hp⟩ := by
  let C := Universal.FamilyPeriodCharts.complexUniversalFamilyCharts D.pel f x
  let H := Universal.HolomorphicTransport.complexUniversalHolomorphicTransport D.pel hg f x
  let R := D.referencePELPointData hg a
  let z₀ : H.compatible.neighborhood := ⟨Intrinsic.FamilyFrames.familyChartCenter C, H.compatible.center⟩
  have hz₀ : Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = R.point := by
    change Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C) ≫ f = R.point
    rw [Family.ChartOpenImage.familyChartParameter_center]
    exact ha
  obtain ⟨O, period, hO, hzO, hOU, hhol, hcenter, hmod⟩ :=
    R.exists_holomorphic_reference_moduli_periods f H z₀ hz₀ hs hdegree
  have hi : InjOn period O := by
    intro z hz w hw he
    obtain ⟨hpz, hzpoint⟩ := hmod z hz
    obtain ⟨hpw, hwpoint⟩ := hmod w hw
    have hab : (⟨period z, hpz⟩ : D.domain) = ⟨period w, hpw⟩ := Subtype.ext he
    rw [hab] at hzpoint
    exact Family.ChartOpenImage.familyChartParameter_injective C (H.compatible.subset_chart (hOU hz))
      (H.compatible.subset_chart (hOU hw)) ((cancel_mono f).mp (hzpoint.trans hwpoint.symm))
  have hd : Module.finrank ℂ (Intrinsic.FamilyFrames.FamilyChartBase C) = Module.finrank ℂ Geometry.ComplexBall.PrescribedSignsB.BallChart := by
    rw [C.dimension, hdim]
    simp [Geometry.ComplexBall.PrescribedSignsB.BallChart]
  let p := InjectiveHolomorphicOpen.injectiveHolomorphicPartialHomeomorph hd hO hhol hi
  have hp : p.MDifferentiable (𝓘(ℂ, Intrinsic.FamilyFrames.FamilyChartBase C)) (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart)) :=
    ⟨mdifferentiableOn_iff_differentiableOn.mpr hhol,
      mdifferentiableOn_iff_differentiableOn.mpr (Finite.DimensionalHolomorphicInverse.injectiveHolomorphicPartialHomeomorph_inverse hd hO hhol hi)⟩
  let c := Family.IntrinsicChart.familyNativeChart C
  let e := c.trans p
  have hxc : x ∈ c.source := Family.IntrinsicChart.familyNativeChart_center_mem C
  have hcx : c x = Intrinsic.FamilyFrames.familyChartCenter C := Family.IntrinsicChart.familyNativeChart_center C
  refine ⟨e, ⟨hxc, ?_⟩, ?_, (Family.IntrinsicChart.familyNativeChart_holomorphic C).trans hp, ?_, ?_⟩
  · change c x ∈ O
    rw [hcx]
    exact hzO
  · change period (c x) = a.val
    rw [hcx]
    exact hcenter
  · intro b hb
    have hbp : b ∈ period '' O := hb.1
    obtain ⟨z, hz, rfl⟩ := hbp
    exact (hmod z hz).choose
  · intro y hy
    have hyO : c y ∈ O := hy.2
    obtain ⟨hpy, hmy⟩ := hmod (c y) hyO
    have hparam : Intrinsic.FamilyFrames.familyChartParameter C (c y) = y := c.left_inv hy.1
    refine ⟨hpy, ?_⟩
    rwa [hparam] at hmy

end

end OAI.RepresentationTheory.Theta.Geometric
