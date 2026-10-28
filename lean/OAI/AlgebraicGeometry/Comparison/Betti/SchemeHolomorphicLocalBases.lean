import OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenRealizationFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenChartRestriction

/-! # Scheme Holomorphic Local Bases -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SchemeHolomorphicLocalBases

noncomputable section

/-! Near each native scheme point, actual algebraic form images are a holomorphic module basis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem affineOpen_manifoldRealization_localBasis (U : X.left.Opens) (hU : IsAffineOpen U)
    (e : OpenPartialHomeomorph
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (RegularSmoothness.NativeModel X))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom))
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U))
    (hx : x ∈ e.source) (n : ℕ) :
    ∃ (W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hW : W ≤ Open.AffineIsoEvaluation.analyticOpen X U),
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x ∈ W ∧
        (∀ p ∈ W, p ∈ (Affine.OpenChartRestriction.affineOpenSchemeChart X U hU e).source) ∧
        ∃ I : Type, Finite I ∧
          ∃ b : Module.Basis I C^∞⟮𝓘(ℂ, RegularSmoothness.NativeModel X), W; 𝓘(ℂ), ℂ⟯ (Holomorphic.DeRhamComplex.forms (RegularSmoothness.NativeModel X) W n),
            ∀ i, ∃ a : Algebraic.Forms.Form Γ(X.left, U) n, b i =
              Holomorphic.HolomorphicPullback.pullback (Opens.inclusion hW) (contMDiff_inclusion (I := 𝓘(ℂ, RegularSmoothness.NativeModel X)) hW) n
                ((Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a) := by
  obtain ⟨V, hV, hxV, I, hI, c, hc⟩ := Affine.OpenRealizationFrames.affineOpen_realization_localBasis X U hU e he x hx n
  let C := Affine.OpenChartRestriction.affineOpenSchemeChart X U hU e
  have hC := Affine.OpenChartRestriction.affineOpenSchemeChart_mem X U hU e he
  refine ⟨Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen C V, Affine.OpenChartRestriction.affineOpenChartPreimage_le X U hU e V, ?_,
    (fun _ hp => hp.1), I, hI,
    Holomorphic.ChartModuleBases.chartPreimageFormBasis C hC V hV n c, ?_⟩
  · refine ⟨⟨x, hx, rfl⟩, ?_⟩
    change ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme _ _ e (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap _ _ x) ∈ V
    rw [ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply]
    exact hxV
  · intro i
    obtain ⟨a, ha⟩ := hc i
    refine ⟨a, ?_⟩
    exact (Holomorphic.ChartModuleBases.chartPreimageFormBasis_apply C hC V hV n c i).trans
      ((congrArg (Holomorphic.HolomorphicPullback.pullback (Holomorphic.ChartMaps.chartForward C V) (Holomorphic.ChartMaps.chartForward_holomorphic C hC V) n) ha).trans
        (Affine.OpenChartRestriction.affineOpenChart_pullback_restrict X U hU e he V hV n
          ((Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a)))

theorem schemePoint_algebraicImages_localBasis (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (n : ℕ) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧
      ∃ (W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hW : W ≤ Open.AffineIsoEvaluation.analyticOpen X U), p ∈ W ∧
        ∃ I : Type, Finite I ∧
          ∃ b : Module.Basis I C^∞⟮𝓘(ℂ, RegularSmoothness.NativeModel X), W; 𝓘(ℂ), ℂ⟯ (Holomorphic.DeRhamComplex.forms (RegularSmoothness.NativeModel X) W n),
            ∀ i, ∃ a : Algebraic.Forms.Form Γ(X.left, U) n, b i =
              Holomorphic.HolomorphicPullback.pullback (Opens.inclusion hW) (contMDiff_inclusion (I := 𝓘(ℂ, RegularSmoothness.NativeModel X)) hW) n
                ((Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a) := by
  obtain ⟨C, ⟨U, hU, e, he, rfl⟩, hp⟩ := ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.exists_schemeRegularChart X p
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨W, hW, hxW, _, h⟩ := affineOpen_manifoldRealization_localBasis X U hU e he x hx n
  exact ⟨U, hU, W, hW, hxW, h⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.SchemeHolomorphicLocalBases
