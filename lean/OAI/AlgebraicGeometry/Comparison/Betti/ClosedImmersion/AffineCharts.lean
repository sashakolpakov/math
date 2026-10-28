import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion

/-! # Affine Charts -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.AffineCharts

noncomputable section

/-! The actual scheme map in lifted affine charts is the original affine algebra comap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped ContDiff

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (φ : X ⟶ Y)
  (V : Y.left.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen (φ.left ⁻¹ᵁ V))
  {n m : ℕ}
  (e : OpenPartialHomeomorph
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V))) (Fin n → ℂ))
  (f : OpenPartialHomeomorph
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)) (Fin m → ℂ))

theorem nativeAffineSchemeChartMap_eq (z : Fin n → ℂ) :
    ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV) f
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ
        ((ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V))
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X (φ.left ⁻¹ᵁ V) hW) e).symm z)) =
    f ((e.symm z).comp (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V)) := by
  rw [ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_symm_apply]
  change ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme _ _ f
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X (φ.left ⁻¹ᵁ V) hW (e.symm z))) = _
  rw [ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square φ V hV hW]
  exact ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV) f ((e.symm z).comp (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V))

theorem nativeAffineSchemeChartMap_contDiffAt
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V)) n)
    (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V) m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V)))
    (hx : x ∈ e.source) (hfx : x.comp (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V) ∈ f.source) :
    ContDiffAt ℂ ω (fun z =>
      ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV) f
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ
          ((ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V))
            (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X (φ.left ⁻¹ᵁ V) hW) e).symm z))) (e x) := by
  simpa only [nativeAffineSchemeChartMap_eq] using
    ComplexPoints.Analytic.SmoothClosedImmersion.contDiffAt_affineChartComap (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V) e f he hf x hx hfx

end

end OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.AffineCharts
