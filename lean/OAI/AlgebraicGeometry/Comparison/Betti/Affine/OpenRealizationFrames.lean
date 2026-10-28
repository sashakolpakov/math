import OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenChartFormNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.SymbolLocalFrames

/-! # Open Realization Frames -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenRealizationFrames

noncomputable section

/-! The original affine-open realization supplies actual local holomorphic bases in every degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem affineOpen_realization_localBasis (U : X.left.Opens) (hU : IsAffineOpen U)
    (e : OpenPartialHomeomorph
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (RegularSmoothness.NativeModel X))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom))
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U))
    (hx : x ∈ e.source) (n : ℕ) :
    ∃ (V : Opens (RegularSmoothness.NativeModel X)) (h : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e), e x ∈ V ∧
      ∃ I : Type, Finite I ∧
        ∃ c : Module.Basis I (Holomorphic.FunctionPure.holomorphicFunctions V) (Holomorphic.DeRhamComplex.forms (RegularSmoothness.NativeModel X) V n),
          ∀ i, ∃ a : Algebraic.Forms.Form Γ(X.left, U) n, c i =
            Holomorphic.HolomorphicPullback.pullback (Opens.inclusion h) (contMDiff_inclusion (I := 𝓘(ℂ, RegularSmoothness.NativeModel X)) h) n
              (Holomorphic.HolomorphicPullback.pullback (OpenChartFormNaturality.affineOpenChartToOpen X U hU e)
                (OpenChartFormNaturality.affineOpenChartToOpen_holomorphic X U hU e he) n
                  ((Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a)) := by
  obtain ⟨V, h, hxV, I, hI, c, hc⟩ := SymbolLocalFrames.affineRegularChart_algebraicImages_localBasis e he x hx n
  refine ⟨V, h, hxV, I, hI, c, ?_⟩
  intro i
  obtain ⟨a, ha⟩ := hc i
  exact ⟨a, ha.trans (congrArg
    (Holomorphic.HolomorphicPullback.pullback (Opens.inclusion h) (contMDiff_inclusion (I := 𝓘(ℂ, RegularSmoothness.NativeModel X)) h) n)
      (OpenChartFormNaturality.openHolomorphicCochainMap_in_affineChart X U hU e he n a))⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenRealizationFrames
