import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleCoefficientFamilyChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.GlobalCoefficientChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.NormalLineNeighborhood

/-! # Retracted Global Coefficient Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.RetractedGlobalCoefficientChart.Construction

noncomputable section

/-! Initial intrinsic coefficient ideals admit actual pointed retracted line charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Polynomial

theorem exists_initial_retracted_global_coefficient_chart
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} (T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b)
    (q : PrimeSpectrum T.ring) (hq : T.normal ∈ q.asIdeal)
    (d : ℕ) (hd : ringKrullDim T.ring ≤ (d + 1 : ℕ)) :
    ∃ T' : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι) b,
      ∃ A : Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T', ringKrullDim A.base ≤ d ∧
        ∃ p : PrimeSpectrum T'.ring, T'.map p = T.map q := by
  let : Algebra.Smooth ℂ T.ring := by
    have hs : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure T.ring) := T.ground ▸ inferInstanceAs (Smooth (T.map ≫ f))
    exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap ℂ T.ring))).mp hs)
  obtain ⟨B, aB, hsB, hdB, S, aS, aBS, aBPS, ht, hpt, he, g, hg, hz, e, p, hp⟩ :=
    Blowups.Smooth.NormalLineNeighborhood.Construction.exists_smooth_normal_line_neighborhood ℂ T.normal T.derivative T.derivative_normal q hq d hd
  let j := Spec.map (CommRingCat.ofHom g.toRingHom) ≫ T.map
  let : Etale (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg
  let : Etale j := inferInstanceAs (Etale (_ ≫ _))
  have hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S := by
    rw [Category.assoc, T.ground, ← Spec.map_comp]
    apply congrArg Spec.map
    ext c
    exact g.commutes c
  let z : S := algebraMap B[X] S Polynomial.X
  have hH : H.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z}) := by
    rw [Scheme.IdealSheafData.comap_comp, T.hypersurface, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom,
      Ideal.map_span, Set.image_singleton]
    exact congrArg (fun v : S => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {v})) hz
  let K := (Ideal.span (Set.range T.family)).map g.toRingHom
  have hK : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K := by
    rw [Scheme.IdealSheafData.comap_comp, T.familyIdeal, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  let D := Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation ℂ (H := B) (R := S)
  have hD : D z = 1 := Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate (H := B) (V := S)
  let T' := GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart.ofEtaleNormal f J H b S j hj z hH K hK D hD
  let A : Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T' := {
    base := B
    algebra := aB
    action := aBS
    lineAction := aBPS
    groundTower := ht
    lineTower := hpt
    lineEtale := he
    normal_eq := rfl
    derivative_eq := rfl
    retraction := e }
  refine ⟨T', A, hdB, p, ?_⟩
  change T.map (PrimeSpectrum.comap g.toRingHom p) = T.map q
  rw [hp]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.RetractedGlobalCoefficientChart.Construction
