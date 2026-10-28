import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Chart
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.GlobalCoefficientEtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientTerminalBound
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport

/-! # Terminal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A terminal retained coefficient bound clears the actual ambient order locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction.terminal_ambient_bound
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J H : X.IdealSheafData}
    [Smooth (H.subschemeι ≫ f)] {C : H.subscheme.IdealSheafData} {n : ℕ}
    {T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C (n + 1)} (A : Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T)
    (hH : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n)
    (hupp : C ≤ GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι)
    (hterminal : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (H.subschemeι ≫ f) C ((n + 1).factorial - 1) = ⊤) :
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap T.map = ⊤ := by
  let K := Ideal.span (Set.range T.family)
  let : Algebra.Smooth ℂ T.ring := by
    have hs : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure T.ring) := T.ground ▸ inferInstanceAs (Smooth (T.map ≫ f))
    exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap ℂ T.ring))).mp hs)
  let : Etale A.baseMap := A.baseMap_etale
  have hd := Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale_affine f J n T.ring T.map T.ground K T.familyIdeal
  have hn : T.normal ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ K n := by
    have h := Scheme.IdealSheafData.comap_mono T.map hH
    change H.comap T.map ≤ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap T.map at h
    rw [T.hypersurface, hd] at h
    exact (Ideal.span_singleton_le_iff_mem _).mp ((Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff _ _).mp h)
  have hc : T.coefficientIdeal ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal ℂ T.normal K (n + 1) := by
    have h := Scheme.IdealSheafData.comap_mono T.coefficientMap hupp
    change C.comap T.coefficientMap ≤
      (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι).comap T.coefficientMap at h
    rw [T.coefficient_eq, Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothCoefficientIdealSheaf_comap_etale_hypersurface_chart f J (n + 1)
      H.subschemeι T.ring T.map T.ground K T.normal T.familyIdeal T.coefficientMap T.coefficient_over] at h
    exact (Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff _ _).mp h
  have ht : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (T.coefficientIdeal.map A.retraction.toRingHom)
      ((n + 1).factorial - 1) = ⊤ := by
    have h := congrArg (fun L : H.subscheme.IdealSheafData => L.comap A.baseMap) hterminal
    rw [Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale_affine (H.subschemeι ≫ f) C ((n + 1).factorial - 1)
      A.base A.baseMap A.baseMap_ground _ A.baseMap_coefficient, Scheme.IdealSheafData.comap_top,
      ← DifferentialUnitGluing.Construction.affineQuotientKernel_top] at h
    exact (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp h
  have hclear := Blowups.Smooth.CoefficientTerminalBound.Construction.retracted_coefficient_terminal_bound_clears_order ℂ T.normal K n hn
    A.retraction.toRingEquiv T.coefficientIdeal hc ht
  rw [hd, hclear, DifferentialUnitGluing.Construction.affineQuotientKernel_top]

theorem GlobalCoefficient.Terminal.Construction.global_retained_coefficient_terminal_clears_order
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData)
    [Smooth (H.subschemeι ≫ f)] (C : H.subscheme.IdealSheafData) (n : ℕ)
    (hH : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n)
    (hupp : C ≤ GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι)
    (hcharts : ∀ x : X, x ∈ H.support →
      ∃ T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C (n + 1), Nonempty (Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T) ∧
        ∃ p : PrimeSpectrum T.ring, T.map p = x)
    (hterminal : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (H.subschemeι ≫ f) C ((n + 1).factorial - 1) = ⊤) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n = ⊤ := by
  apply top_le_iff.mp
  apply Pointed.EtaleIdealSheafContainment.Construction.idealSheaf_le_of_pointed_etale_charts f
  intro x
  by_cases hx : x ∈ H.support
  · obtain ⟨T, ⟨A⟩, p, hp⟩ := hcharts x hx
    refine ⟨T.ring, T.algebra, T.map, T.etale, T.ground, p, hp, ?_⟩
    rw [A.terminal_ambient_bound hH hupp hterminal]
    exact le_top
  · obtain ⟨V, hV, hxV, hVH⟩ := exists_isAffineOpen_mem_and_subset (U := H.support.compl) (x := x) hx
    let U : X.affineOpens := ⟨V, hV⟩
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    have hxrange : x ∈ U.2.fromSpec.opensRange := by rw [U.2.opensRange_fromSpec]; exact hxV
    obtain ⟨p, hp⟩ := hxrange
    have hunit : (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap U.2.fromSpec = ⊤ := by
      apply ControlledIdealKernel.Construction.idealSheaf_comap_eq_top_of_avoids_support
      intro q hq
      have hmem : U.2.fromSpec q ∈ U.1 := by
        have hr : U.2.fromSpec q ∈ U.2.fromSpec.opensRange := ⟨q, rfl⟩
        rwa [U.2.opensRange_fromSpec] at hr
      exact hVH hmem (Scheme.IdealSheafData.support_antitone hH hq)
    refine ⟨Γ(X, U), inferInstance, U.2.fromSpec, inferInstance,
      (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U).symm, p, hp, ?_⟩
    rw [hunit]
    exact le_top

end

end OAI.AlgebraicGeometry.Resolution.Blowups
