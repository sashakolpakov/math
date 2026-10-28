import OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeHolomorphicKernel
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenIntrinsicRegularChart

/-! # Holomorphic Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.HolomorphicStalk

noncomputable section

/-! Actual holomorphic stalks of every smooth closed immersion are surjective quotients by the original local defining equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (φ : X ⟶ Y) [IsClosedImmersion φ.left]

theorem analyticHolomorphicStalkPullback_surjective (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Surjective (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback φ p) := by
  obtain ⟨V, hV, x, hxp⟩ := ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.exists_nativeClosedImmersion_affineReduction φ p
  subst p
  let W := φ.left ⁻¹ᵁ V
  let hW : IsAffineOpen W := hV.preimage φ.left
  let p := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X W hW x
  let h := ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V
  obtain ⟨e, he, hx⟩ := Affine.OpenIntrinsicRegularChart.affineOpen_exists_nativeRegularChart X W hW x
  obtain ⟨f, hf, hfx⟩ := Affine.OpenIntrinsicRegularChart.affineOpen_exists_nativeRegularChart Y V hV (x.comp h)
  have hq := ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square φ V hV hW x
  let eS := Affine.SchemeStalkCenters.affineSchemeChartStalkEquivAt Y V hV f hf (x.comp h) hfx
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ p) hq
  let eT := Affine.SchemeStalkCenters.affineSchemeChartStalkEquivAt X W hW e he x hx p rfl
  intro b
  obtain ⟨a, ha⟩ := Affine.ClosedGermQuotient.AnalyticLocal.affineChartGermPullback_surjective h e f he hf x hx hfx
    (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_surjective φ V hV) (eT b)
  refine ⟨eS.symm a, eT.injective ?_⟩
  have hm := Affine.SchemeStalkPullbackNormalization.affineSchemeChartStalkEquiv_pullback φ V hV hW e f he hf x hx hfx (eS.symm a)
  change eT (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback φ p (eS.symm a)) =
    Affine.ClosedGermQuotient.AnalyticLocal.affineChartGermPullback h e f he hf x hx hfx (eS (eS.symm a)) at hm
  exact hm.trans ((congrArg (Affine.ClosedGermQuotient.AnalyticLocal.affineChartGermPullback h e f he hf x hx hfx)
    (eS.apply_symm_apply a)).trans ha)

theorem analyticHolomorphicStalkPullback_exists_affine_kernel (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ (V : Y.left.Opens) (_hV : IsAffineOpen V)
      (hpV : Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ p) ∈ V),
      RingHom.ker (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback φ p) =
        Ideal.map ((ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ p)).comp
          (Y.left.presheaf.germ V (Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ p)) hpV).hom)
          (RingHom.ker (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V).toRingHom) := by
  obtain ⟨V, hV, x, hxp⟩ := ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.exists_nativeClosedImmersion_affineReduction φ p
  subst p
  let W := φ.left ⁻¹ᵁ V
  let hW : IsAffineOpen W := hV.preimage φ.left
  let p := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X W hW x
  let h := ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V
  obtain ⟨e, he, hx⟩ := Affine.OpenIntrinsicRegularChart.affineOpen_exists_nativeRegularChart X W hW x
  obtain ⟨f, hf, hfx⟩ := Affine.OpenIntrinsicRegularChart.affineOpen_exists_nativeRegularChart Y V hV (x.comp h)
  have hq := ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square φ V hV hW x
  have hpV : Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ p) ∈ V := by
    rw [hq]
    have hm : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Y V hV (x.comp h) ∈
        Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Y V hV) := ⟨x.comp h, rfl⟩
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hm
    exact hm
  exact ⟨V, hV, hpV, Affine.SchemeHolomorphicKernel.analyticHolomorphicStalkPullback_ker_affine φ V hV hW e f he hf x hx hfx p rfl hpV⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.HolomorphicStalk
