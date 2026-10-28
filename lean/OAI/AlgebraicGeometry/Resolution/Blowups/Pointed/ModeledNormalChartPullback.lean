import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.NormalChartEtaleTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.NormalChartIntrinsicData
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.AmbientCarrierRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CarrierBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PullbackCenter

/-! # Modeled Normal Chart Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A modeled normal chart pulls back to pointed integral normal charts under an actual étale base map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart.normal_mem_at_order_point
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    {β : Type} {D : β → X.IdealSheafData} {x : X} (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart f J n D x)
    (p : PrimeSpectrum C.ring) (hp : C.map p ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support) :
    C.normal ∈ p.asIdeal := by
  have he := Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale_affine f J n C.ring C.map C.ground C.ideal C.ideal_eq
  have hN := (Coefficient.ChartSupport.Construction.affine_center_le_prime_iff_global_support _ C.ring C.map _ he p).mpr hp
  exact hN C.normal_mem

theorem Pointed.ModeledNormalChartPullback.Construction.exists_pointed_integral_modeled_normal_chart_pullback
    {X V : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    {β : Type} {D : β → X.IdealSheafData} {x : X}
    (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x) (q : V ⟶ X) [Etale q]
    (y : V) (p : PrimeSpectrum C.chart.ring) (hp : C.chart.map p = q y)
    (horder : q y ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support) :
    ∃ B : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart (q ≫ f) (J.comap q) n (fun l => (D l).comap q) y,
      IsDomain B.chart.ring ∧ IsIntegral B.chart.nativeCarrier.subscheme ∧
      ∃ φ : C.chart.ring →ₐ[ℂ] B.chart.ring, φ.toRingHom.Etale ∧
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ C.chart.map = B.chart.map ≫ q ∧
        PrimeSpectrum.comap φ.toRingHom B.chart.point = p ∧
        B.chart.normal = φ C.chart.normal ∧ B.chart.ideal = C.chart.ideal.map φ.toRingHom ∧
        ∀ l, B.chart.equations l = φ (C.chart.equations l) := by
  let W := pullback C.chart.map q
  let a : W ⟶ Spec C.chart.ring := pullback.fst C.chart.map q
  let b : W ⟶ V := pullback.snd C.chart.map q
  obtain ⟨z, hz, hzy⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback C.chart.map q) p y hp
  let H := C.chart.nativeCarrier
  let H0 := H.comap a
  let g := a ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure C.chart.ring
  let : Smooth (H.subschemeι ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure C.chart.ring) := by
    rw [← C.chart.ground]
    exact C.chart.nativeCarrier_smooth
  let : Smooth (H0.subschemeι ≫ g) := Blowups.Etale.PullbackCenter.Construction.idealSheaf_comap_etale_smooth_center (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure C.chart.ring) a H
  have hpH : p ∈ H.support := by
    change p ∈ ((Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C.chart.normal})).support : Set (Spec (.of C.chart.ring)))
    rw [Coefficient.ChartSupport.Construction.affineQuotientKernel_support]
    exact (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr
      (C.chart.normal_mem_at_order_point p (hp.symm ▸ horder))
  have hzH : z ∈ H0.support := by
    rw [Scheme.IdealSheafData.support_comap]
    change a z ∈ H.support
    rwa [hz]
  obtain ⟨R, l, hl, hR, hH, pR, hpR⟩ := Integral.AmbientCarrierRefinement.Construction.exists_integral_affine_ambient_carrier_refinement g H0 z hzH
  let : IsOpenImmersion l := hl
  let u := l ≫ a
  let j := l ≫ b
  let ψ := (Spec.preimage u).hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) = u := Spec.map_preimage u
  let : Algebra ℂ R := (ψ.comp (algebraMap ℂ C.chart.ring)).toAlgebra
  let φ : C.chart.ring →ₐ[ℂ] R := { __ := ψ, commutes' := fun _ => rfl }
  have hφ : φ.toRingHom.Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    exact inferInstanceAs (Etale u)
  have hcomm : u ≫ C.chart.map = j ≫ q := by
    dsimp only [u, j, a, b]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hg : j ≫ (q ≫ f) = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R := by
    rw [← Category.assoc, ← hcomm, Category.assoc, C.chart.ground, ← hψ]
    exact Affine.IdealOverlapEquality.Construction.complexSpecStructure_specMap_algHom C.chart.ring R φ
  have hJ : (J.comap q).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (C.chart.ideal.map φ.toRingHom) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hcomm, Scheme.IdealSheafData.comap_comp,
      C.chart.ideal_eq, ← hψ, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  have hD (i : β) : ((D i).comap q).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {φ (C.chart.equations i)}) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hcomm, Scheme.IdealSheafData.comap_comp,
      C.chart.component, ← hψ, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Ideal.map_span, Set.image_singleton]
  have hpoint : j pR = y := by
    change b (l pR) = y
    rw [hpR]
    exact hzy
  let B := C.transportEtale (q ≫ f) (J.comap q) (fun i => (D i).comap q) R φ hφ j hg hJ hD pR hpoint
  have hcarrier : IsIntegral B.chart.nativeCarrier.subscheme := by
    change IsIntegral ((H.comap a).comap l).subscheme at hH
    rw [← Scheme.IdealSheafData.comap_comp] at hH
    change IsIntegral ((Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C.chart.normal})).comap u).subscheme at hH
    rw [← hψ, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Ideal.map_span, Set.image_singleton] at hH
    exact hH
  refine ⟨B, (affine_isIntegral_iff R).mp hR, hcarrier, φ, hφ, ?_, ?_, rfl, rfl, fun _ => rfl⟩
  · change Spec.map (CommRingCat.ofHom ψ) ≫ C.chart.map = j ≫ q
    rw [hψ]
    exact hcomm
  · change Spec.map (CommRingCat.ofHom ψ) pR = p
    rw [hψ]
    change a (l pR) = p
    rw [hpR]
    exact hz

end

end OAI.AlgebraicGeometry.Resolution.Blowups
