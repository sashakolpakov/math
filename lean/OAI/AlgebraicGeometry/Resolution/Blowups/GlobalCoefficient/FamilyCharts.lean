import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientFamilyCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleIdealSheafContainment
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledIdealKernel

/-! # Family Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.FamilyCharts.Construction

noncomputable section

/-! Actual local retained coefficient families and their global permissible-center criterion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- An actual étale ambient chart, its actual hypersurface map, and a fixed
normal-derivative family lying in the retained native coefficient ideal. -/
structure GlobalCoefficientFamilyChart {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (J H : X.IdealSheafData) (C : H.subscheme.IdealSheafData) (b : ℕ) where
  ring : CommRingCat
  algebra : Algebra ℂ ring
  map : Spec ring ⟶ X
  etale : Etale map
  ground : map ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure ring
  normal : ring
  hypersurface : H.comap map = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {normal})
  derivative : Derivation ℂ ring ring
  derivative_normal : derivative normal = 1
  familyIndex : Type
  family : familyIndex → ring
  familyIdeal : J.comap map = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span (Set.range family))
  coefficientMap : Spec (.of (ring ⧸ Ideal.span {normal})) ⟶ H.subscheme
  coefficient_over : coefficientMap ≫ H.subschemeι =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {normal}))) ≫ map
  coefficientIdeal : Ideal (ring ⧸ Ideal.span {normal})
  coefficient_eq : C.comap coefficientMap = Affine.QuotientKernel.Construction.affineQuotientKernel coefficientIdeal
  lower : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal derivative normal family b ≤ coefficientIdeal

attribute [instance] GlobalCoefficientFamilyChart.algebra GlobalCoefficientFamilyChart.etale

theorem GlobalCoefficientFamilyChart.permissible
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} (T : GlobalCoefficientFamilyChart f J H C b)
    (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] (hHI : H ≤ I)
    (hC : C ≤ (I.comap H.subschemeι) ^ b.factorial) :
    J.comap T.map ≤ (I ^ b).comap T.map := by
  obtain ⟨A, hA⟩ := Affine.KernelOrderEquiv.Construction.exists_affineQuotientKernel (I.comap T.map)
  exact Blowups.Etale.CoefficientFamilyCenter.Construction.etale_coefficient_family_center_permissible f I J H hHI C b hC T.ring T.map T.ground
    A hA.symm T.normal T.hypersurface T.derivative T.derivative_normal T.family T.familyIdeal
    T.coefficientMap T.coefficient_over T.coefficientIdeal T.coefficient_eq T.lower

/-- Pointed retained coefficient charts along the whole carrier suffice to
lift every smooth permissible coefficient center to a global ambient center. -/
theorem global_center_permissible_of_coefficient_family_charts
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J H : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] (hHI : H ≤ I) (C : H.subscheme.IdealSheafData) (b : ℕ)
    (hcharts : ∀ x : X, x ∈ H.support → ∃ T : GlobalCoefficientFamilyChart f J H C b,
      ∃ p : PrimeSpectrum T.ring, T.map p = x)
    (hC : C ≤ (I.comap H.subschemeι) ^ b.factorial) : J ≤ I ^ b := by
  apply Pointed.EtaleIdealSheafContainment.Construction.idealSheaf_le_of_pointed_etale_charts f
  intro x
  by_cases hx : x ∈ H.support
  · obtain ⟨T, p, hp⟩ := hcharts x hx
    exact ⟨T.ring, T.algebra, T.map, T.etale, T.ground, p, hp, T.permissible I hHI hC⟩
  · obtain ⟨V, hV, hxV, hVH⟩ := exists_isAffineOpen_mem_and_subset
      (U := H.support.compl) (x := x) hx
    let U : X.affineOpens := ⟨V, hV⟩
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    have hxrange : x ∈ U.2.fromSpec.opensRange := by rw [U.2.opensRange_fromSpec]; exact hxV
    obtain ⟨p, hp⟩ := hxrange
    have hunit : I.comap U.2.fromSpec = ⊤ := by
      apply ControlledIdealKernel.Construction.idealSheaf_comap_eq_top_of_avoids_support
      intro q hq
      have hmem : U.2.fromSpec q ∈ U.1 := by
        have hr : U.2.fromSpec q ∈ U.2.fromSpec.opensRange := ⟨q, rfl⟩
        rwa [U.2.opensRange_fromSpec] at hr
      exact hVH hmem (Scheme.IdealSheafData.support_antitone hHI hq)
    refine ⟨Γ(X, U), inferInstance, U.2.fromSpec, inferInstance,
      (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U).symm, p, hp, ?_⟩
    rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, hunit, ← Scheme.IdealSheafData.one_eq_top, one_pow,
      Scheme.IdealSheafData.one_eq_top]
    exact le_top

theorem global_smooth_center_iff_retained_coefficient_center
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J H : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] (hHI : H ≤ I) (C : H.subscheme.IdealSheafData) (b : ℕ)
    (hcharts : ∀ x : X, x ∈ H.support → ∃ T : GlobalCoefficientFamilyChart f J H C b,
      ∃ p : PrimeSpectrum T.ring, T.map p = x)
    (hupp : C ≤ CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι) :
    J ≤ I ^ b ↔ C ≤ (I.comap H.subschemeι) ^ b.factorial := by
  constructor
  · intro hp
    exact hupp.trans (CoefficientSheaf.Construction.smoothCoefficientIdealSheaf_le_of_order f I J b H.subschemeι hp)
  · exact global_center_permissible_of_coefficient_family_charts f I J H hHI C b hcharts

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.FamilyCharts.Construction
