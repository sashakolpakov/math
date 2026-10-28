import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.NormalChartRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.AmbientCarrierRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport

/-! # Modeled Normal Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Modeled normal charts refine to integral affine ambient schemes and integral native maximal-contact carriers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart.order_at_point
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    {β : Type} {D : β → X.IdealSheafData} {x : X}
    (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart f J n D x)
    (hx : x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ C.ideal n ≤ C.point.asIdeal := by
  have he := Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale_affine f J n C.ring C.map C.ground C.ideal C.ideal_eq
  exact (Coefficient.ChartSupport.Construction.affine_center_le_prime_iff_global_support _ C.ring C.map _ he C.point).mpr
    (C.point_over.symm ▸ hx)

theorem GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart.exists_integral_refinement
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    {β : Type} {D : β → X.IdealSheafData} {x : X}
    (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x) (hx : C.chart.normal ∈ C.chart.point.asIdeal) :
    ∃ B : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x,
      IsDomain B.chart.ring ∧ IsIntegral (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {B.chart.normal})).subscheme := by
  let H := Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C.chart.normal})
  let : Algebra.Smooth ℂ (C.chart.ring ⧸ Ideal.span {C.chart.normal}) := C.chart.coefficientBoundary.smooth
  let : Smooth (H.subschemeι ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure C.chart.ring) :=
    Global.PointedSmoothCenter.Construction.affineQuotientKernel_complex_subscheme_smooth C.chart.ring (Ideal.span {C.chart.normal})
  have hp : C.chart.point ∈ H.support := by
    change C.chart.point ∈ ((Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C.chart.normal})).support : Set (Spec (.of C.chart.ring)))
    rw [Coefficient.ChartSupport.Construction.affineQuotientKernel_support]
    exact (Ideal.span_singleton_le_iff_mem C.chart.point.asIdeal).mpr hx
  obtain ⟨R, j, hj, hR, hH, p, hpj⟩ := Integral.AmbientCarrierRefinement.Construction.exists_integral_affine_ambient_carrier_refinement
    (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure C.chart.ring) H C.chart.point hp
  let ψ := (Spec.preimage j).hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) = j := Spec.map_preimage j
  let : Algebra ℂ R := (ψ.comp (algebraMap ℂ C.chart.ring)).toAlgebra
  let φ : C.chart.ring →ₐ[ℂ] R := { __ := ψ, commutes' := fun _ => rfl }
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := hψ.symm ▸ hj
  have hpoint : PrimeSpectrum.comap φ.toRingHom p = C.chart.point := by
    change Spec.map (CommRingCat.ofHom ψ) p = C.chart.point
    rw [hψ]
    exact hpj
  let B := C.refine R φ p hpoint
  have hcarrier : IsIntegral (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {φ C.chart.normal})).subscheme := by
    change IsIntegral (H.comap j).subscheme at hH
    rw [← hψ, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Ideal.map_span, Set.image_singleton] at hH
    exact hH
  exact ⟨B, (affine_isIntegral_iff R).mp hR, hcarrier⟩

theorem Integral.ModeledNormalChart.Construction.exists_integral_global_boundary_modeled_normal_chart
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {β : Type} [Fintype β]
    {D : β → X.IdealSheafData} (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    (J : X.IdealSheafData) (n : ℕ) (hbound : B.logarithmicIdeal J (n + 1) = ⊤)
    (x : X) (hx : x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support) :
    ∃ C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x,
      IsDomain C.chart.ring ∧ IsIntegral (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C.chart.normal})).subscheme := by
  obtain ⟨C⟩ := GlobalBoundary.ModeledNormalChart.Construction.exists_global_boundary_modeled_normal_chart B J n hbound x hx
  exact C.exists_integral_refinement ((C.chart.order_at_point hx) C.chart.normal_mem)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
