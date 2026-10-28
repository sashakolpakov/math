import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.IntrinsicReferenceModuliPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallChart
import OAI.RepresentationTheory.Theta.Geometric.Finite.DimensionalHolomorphicInverse

/-! # Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! At a reference point of a smooth integral surface in the fine model,
the exact original reference period is a native holomorphic local chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold

open OAI.RepresentationTheory.Theta.Geometric.Finite.DimensionalHolomorphicInverse

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
attribute [local irreducible] Models.FinePELModel.complexTestFamily

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ M.complexFiber κ) [Mono f]

theorem Models.FinePELModel.exists_native_reference_moduli_chart
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (a : P.domain)
    (ha : x ≫ f = M.referencePoint hM κ hP hκ a) :
    ∃ e : OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) Geometry.ComplexBall.PrescribedSignsB.BallChart,
      x ∈ e.source ∧ e x = a.val ∧
      e.MDifferentiable (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ))
        (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart)) ∧ e.target ⊆ P.domain ∧
      ∀ y ∈ e.source, ∃ hp : e y ∈ P.domain,
        y ≫ f = M.referencePoint hM κ hP hκ ⟨e y, hp⟩ := by
  obtain ⟨C, F, ⟨H⟩⟩ := Intrinsic.HolomorphicTransport.exists_native_family_holomorphic_transport
    (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action x (NeZero.pos N)
  let z₀ : H.compatible.neighborhood := ⟨RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C, H.compatible.center⟩
  have hz₀ : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = M.referencePoint hM κ hP hκ a := by
    change RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C) ≫ f = _
    rw [RepresentationTheory.Theta.Geometric.Family.ChartOpenImage.familyChartParameter_center]
    exact ha
  obtain ⟨O, period, hO, hzO, hOU, hhol, hcenter, hmod⟩ :=
    M.exists_holomorphic_native_reference_moduli_periods hM κ hP hκ f a H z₀ hz₀ hs hdegree
  have hi : Set.InjOn period O := by
    intro z hz w hw he
    obtain ⟨hpz, hzpoint⟩ := hmod z hz
    obtain ⟨hpw, hwpoint⟩ := hmod w hw
    have hab : (⟨period z, hpz⟩ : P.domain) = ⟨period w, hpw⟩ := Subtype.ext he
    rw [hab] at hzpoint
    exact RepresentationTheory.Theta.Geometric.Family.ChartOpenImage.familyChartParameter_injective C (H.compatible.subset_chart (hOU hz))
      (H.compatible.subset_chart (hOU hw)) ((cancel_mono f).mp (hzpoint.trans hwpoint.symm))
  have hd : Module.finrank ℂ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C) = Module.finrank ℂ Geometry.ComplexBall.PrescribedSignsB.BallChart := by
    rw [C.dimension, hdim]
    simp only [Geometry.ComplexBall.PrescribedSignsB.BallChart, Module.finrank_pi, Fintype.card_fin]
  let p := RepresentationTheory.Theta.Geometric.InjectiveHolomorphicOpen.injectiveHolomorphicPartialHomeomorph hd hO hhol hi
  have hp : p.MDifferentiable (𝓘(ℂ, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart)) :=
    ⟨mdifferentiableOn_iff_differentiableOn.mpr hhol,
      mdifferentiableOn_iff_differentiableOn.mpr
        (RepresentationTheory.Theta.Geometric.Finite.DimensionalHolomorphicInverse.injectiveHolomorphicPartialHomeomorph_inverse hd hO hhol hi)⟩
  let c := RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart C
  let e := c.trans p
  have hxc : x ∈ c.source := RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart_center_mem C
  have hcx : c x = RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C := RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart_center C
  refine ⟨e, ⟨hxc, ?_⟩, ?_, (RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart_holomorphic C).trans hp, ?_, ?_⟩
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
    have hparam : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (c y) = y := c.left_inv hy.1
    refine ⟨hpy, ?_⟩
    rwa [hparam] at hmy

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
