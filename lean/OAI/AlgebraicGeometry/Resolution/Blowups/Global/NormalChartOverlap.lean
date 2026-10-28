import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.NormalChartOverlap
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.ModeledNormalChart

/-! # Normal Chart Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.NormalChartOverlap.Construction

noncomputable section

/-! Integral modeled normal charts supply the initial overlap data required by whole-program gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_tangent_overlap_of_global_normal_charts
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    {β : Type} {D : β → X.IdealSheafData} {x y : X}
    (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x) (C' : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D y)
    [IsDomain C.chart.ring]
    [IsIntegral (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C.chart.normal})).subscheme]
    [IsIntegral (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C'.chart.normal})).subscheme]
    (p : PrimeSpectrum C.chart.ring) (q : PrimeSpectrum C'.chart.ring) (hpq : C.chart.map p = C'.chart.map q)
    (hp : C.chart.map p ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support) :
    ∃ A : TangentCarrierData.Construction.TangentCarrierOverlapData (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure C.chart.ring)
      (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ C.chart.ideal n))
      (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C.chart.normal}))
      (fun i => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C.chart.equations i}))
      (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure C'.chart.ring) (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ C'.chart.ideal n))
      (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C'.chart.normal}))
      (fun i => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C'.chart.equations i})) n,
      ∃ a : A.ambient, A.left a = p ∧ A.right a = q ∧ A.left ≫ C.chart.map = A.right ≫ C'.chart.map := by
  let : IsNoetherianRing C.chart.ring := Algebra.FiniteType.isNoetherianRing ℂ C.chart.ring
  have he := Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale_affine f J n C.chart.ring C.chart.map
    C.chart.ground C.chart.ideal C.chart.ideal_eq
  have hord := (Coefficient.ChartSupport.Construction.affine_center_le_prime_iff_global_support _ C.chart.ring C.chart.map _ he p).mpr hp
  exact Modeled.NormalChartOverlap.Construction.exists_tangent_overlap_of_modeled_normal_charts f J D C.chart.ring C'.chart.ring
    C.chart.map C'.chart.map C.chart.ground C'.chart.ground C.chart.ideal C'.chart.ideal
    C.chart.ideal_eq C'.chart.ideal_eq C.chart.equations C'.chart.equations C.chart.component C'.chart.component
    C.model C.chart.normal C'.chart.normal n C.chart.derivative C'.chart.derivative
    C.chart.derivative_normal C'.chart.derivative_normal C.derivative_tangent C'.derivative_tangent
    C.chart.normal_mem C'.chart.normal_mem p q hpq hord

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.NormalChartOverlap.Construction
