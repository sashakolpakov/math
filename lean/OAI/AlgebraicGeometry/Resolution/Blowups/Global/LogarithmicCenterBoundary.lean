import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.ModeledNormalChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.CenterRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.CenterEtaleRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.BoundRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterCoordinateChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterSupportCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.BoundaryCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoefficientBoundaryCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.CoverDimension

/-! # Logarithmic Center Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Full logarithmic bounds make canonical component and surface tangent centers boundary-compatible. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.componentBoundaryAtlas_of_log_bound
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (E : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
    (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (hlog : B.logarithmicIdeal J (n + 1) = ⊤) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f A.center D := by
  let : Smooth (A.center.subschemeι ≫ f) := A.center_smooth
  have hTI := Global.OrderLocusPreservation.Construction.global_tangent_le_permissible_center f J A.center n A.center_permissible
  apply Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofCenterCharts f A.center D E
  intro x hx
  have hxT : x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support :=
    Scheme.IdealSheafData.support_antitone hTI hx
  obtain ⟨C⟩ := GlobalBoundary.ModeledNormalChart.Construction.exists_global_boundary_normal_chart B J n hlog x hxT
  let : Algebra ℚ C.ring := ((algebraMap ℂ C.ring).comp (algebraMap ℚ ℂ)).toAlgebra
  let : Algebra.Smooth ℂ (C.ring ⧸ Ideal.span {C.normal}) := C.coefficientBoundary.smooth
  let N : Component.CenterChoice.Construction.ComponentCenterChoice ℂ C.ring C.ideal n :=
    .normal C.normal C.derivative C.derivative_normal C.normal_mem
  have hK : A.center.comap C.map = Affine.QuotientKernel.Construction.affineQuotientKernel N.center :=
    A.center_restrict_etale C.ring C.map C.ground C.ideal C.ideal_eq N
  have hNp : N.center ≤ C.point.asIdeal :=
    (Coefficient.ChartSupport.Construction.affine_center_le_prime_iff_global_support A.center C.ring C.map N.center hK C.point).mpr
      (C.point_over.symm ▸ hx)
  have hc := Component.BoundaryCenter.Construction.coefficientComponentCenter_boundary_admissible C.equations C.normal
    (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ C.ideal n) (n + 1) C.fullBoundary
  obtain ⟨M⟩ := hc C.point hNp
  let V := Global.MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.ofCoordinateChart f A.center D C.ring C.map C.ground
    N.center hK C.equations C.component ∅ C.point M
  exact ⟨V, M.chart.point, (congrArg C.map M.chart.point_over).trans C.point_over⟩

def GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceBoundaryAtlas_of_log_bound
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (hb : ∀ i, (A.choice i).HasBound (ℓ + 1))
    (hd : topologicalKrullDim X ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (E : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
    (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (hlog : B.logarithmicIdeal J (n + 1) = ⊤) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (A.surfaceCenter ℓ hb (A.chart_dimension_le 2 hd) hlevel) D := by
  let hdA := A.chart_dimension_le 2 hd
  let I := A.surfaceCenter ℓ hb hdA hlevel
  let : Smooth (I.subschemeι ≫ f) := A.surfaceCenter_isSmooth ℓ hb hdA hlevel
  have hTI := Global.OrderLocusPreservation.Construction.global_tangent_le_permissible_center f J I n (A.surfaceCenter_isPermissible ℓ hb hdA hlevel)
  apply Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofCenterCharts f I D E
  intro x hx
  have hxT : x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support :=
    Scheme.IdealSheafData.support_antitone hTI hx
  obtain ⟨C⟩ := GlobalBoundary.ModeledNormalChart.Construction.exists_global_boundary_normal_chart B J n hlog x hxT
  let : Algebra ℚ C.ring := ((algebraMap ℂ C.ring).comp (algebraMap ℚ ℂ)).toAlgebra
  let : IsNoetherianRing C.ring := Algebra.FiniteType.isNoetherianRing ℂ C.ring
  let N : Component.CenterChoice.Construction.ComponentCenterChoice ℂ C.ring C.ideal n :=
    .normal C.normal C.derivative C.derivative_normal C.normal_mem
  have hCbound : N.HasBound (ℓ + 1) :=
    A.hasBound_restrict_etale (ℓ + 1) hb C.ring C.map C.ground C.ideal C.ideal_eq N
  let S := N.toSurfaceTangentChoice ℓ hCbound
  have hdC : ringKrullDim C.ring ≤ 2 := (Open.CoverDimension.Construction.ringKrullDim_le_of_affine_open_map C.ring C.map).trans hd
  have hK : I.comap C.map = Affine.QuotientKernel.Construction.affineQuotientKernel S.center :=
    A.surfaceCenter_restrict_etale ℓ hb hdA hlevel C.ring C.map C.ground C.ideal C.ideal_eq S hdC
  have hSp : S.center ≤ C.point.asIdeal :=
    (Coefficient.ChartSupport.Construction.affine_center_le_prime_iff_global_support I C.ring C.map S.center hK C.point).mpr
      (C.point_over.symm ▸ hx)
  have hdQ : ringKrullDim (C.ring ⧸ Ideal.span {C.normal}) ≤ 1 :=
    NormalQuotientDimension.Construction.normal_quotient_dimension_induction C.derivative C.normal C.derivative_normal 1 hdC
  obtain ⟨F, M⟩ := Curve.CoefficientBoundaryCenter.Construction.curve_coefficient_tangent_boundary_chart C.ring C.normal C.derivative
    C.derivative_normal (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ C.ideal n) (n + 1) ℓ hdQ
    C.equations C.coefficientBoundary hCbound C.point hSp
  obtain ⟨M⟩ := M
  let V := Global.MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.ofCoordinateChart f I D C.ring C.map C.ground
    S.center hK C.equations C.component F C.point M
  exact ⟨V, M.chart.point, (congrArg C.map M.chart.point_over).trans C.point_over⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
