import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.ModeledNormalChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.NormalChartIntrinsicData
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.BoundRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ZeroCenter

/-! # Normal Chart Coefficient Nonzero -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Finite coefficient bounds exclude zero intrinsic coefficients on pointed normal carriers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem NormalChartCoefficientNonzero.Construction.affine_native_coefficient_ne_bot_of_bound
    (R : CommRingCat) [Algebra ℂ R] [Algebra.Smooth ℂ R]
    (z : R) [Algebra.Smooth ℂ (R ⧸ Ideal.span {z})]
    (J : Ideal R) (b m : ℕ) (hb : 0 < b)
    (p : PrimeSpectrum R) (hp : z ∈ p.asIdeal)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal ℂ z J b) m = ⊤) :
    GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (Affine.QuotientKernel.Construction.affineQuotientKernel J) b
      (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})).subschemeι ≠ ⊥ := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℂ R
  let : Smooth ((Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})).subschemeι ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) :=
    Global.PointedSmoothCenter.Construction.affineQuotientKernel_complex_subscheme_smooth R (Ideal.span {z})
  have hproper : Ideal.span ({z} : Set R) ≠ ⊤ := by
    intro he
    exact p.isPrime.ne_top (top_le_iff.mp (he ▸ (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hp))
  let : Nontrivial (R ⧸ Ideal.span {z}) := Ideal.Quotient.nontrivial_iff.mpr hproper
  intro hz
  have horder := (GlobalCoefficient.ZeroCenter.Construction.smoothCoefficientIdealSheaf_eq_bot_iff (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R)
    (Affine.QuotientKernel.Construction.affineQuotientKernel J) (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})) b hb).mp hz
  rw [← Affine.QuotientKernel.Construction.affineQuotientKernel_pow] at horder
  have hJ : J ≤ Ideal.span {z} ^ b := (Affine.KernelOrderEquiv.Construction.affineQuotientKernel_le_iff _ _).mp horder
  have hC := Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal_le_of_order ℂ z J (Ideal.span {z}) b hJ
  rw [Ideal.map_quotient_self, Ideal.bot_pow (Nat.factorial_ne_zero b)] at hC
  rw [le_bot_iff.mp hC, DifferentialSaturation.Construction.iteratedRelativeDifferentialIdeal_bot] at hbound
  exact bot_ne_top hbound

theorem GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart.native_coefficient_ne_bot_of_atlas_bound
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    {β : Type} {D : β → X.IdealSheafData} {x : X}
    (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart f J n D x)
    (hx : x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support)
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (m : ℕ) (hA : ∀ i, (A.choice i).HasBound m) :
    GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure C.ring)
      (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ C.ideal n)) (n + 1)
        C.nativeCarrier.subschemeι ≠ ⊥ := by
  let : Algebra ℚ C.ring := ((algebraMap ℂ C.ring).comp (algebraMap ℚ ℂ)).toAlgebra
  let : Algebra.Smooth ℂ (C.ring ⧸ Ideal.span {C.normal}) := C.coefficientBoundary.smooth
  let N : Component.CenterChoice.Construction.ComponentCenterChoice ℂ C.ring C.ideal n :=
    .normal C.normal C.derivative C.derivative_normal C.normal_mem
  have hbound := A.hasBound_restrict_etale m hA C.ring C.map C.ground C.ideal C.ideal_eq N
  exact NormalChartCoefficientNonzero.Construction.affine_native_coefficient_ne_bot_of_bound C.ring C.normal
    (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ C.ideal n) (n + 1) m (Nat.succ_pos n) C.point
    ((C.order_at_point hx) C.normal_mem) hbound

end

end OAI.AlgebraicGeometry.Resolution.Blowups
