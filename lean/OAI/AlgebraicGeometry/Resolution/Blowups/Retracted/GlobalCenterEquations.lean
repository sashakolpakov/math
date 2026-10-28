import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Chart

/-! # Global Center Equations -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Retracted

noncomputable section

/-! A native center contained in the carrier has actual horizontal coefficient equations on every retracted chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction.center_equations
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} {T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b}
    (A : GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T) (I : X.IdealSheafData) (hHI : H ≤ I)
    (L : Ideal T.ring) (hL : I.comap T.map = Affine.QuotientKernel.Construction.affineQuotientKernel L) :
    let K := (L.map (Ideal.Quotient.mk (Ideal.span {T.normal}))).map A.retraction.toRingHom
    (I.comap H.subschemeι).comap A.baseMap = Affine.QuotientKernel.Construction.affineQuotientKernel K ∧
      Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := T.ring) K = L := by
  intro K
  have hnormal : Ideal.span {T.normal} ≤ L := by
    have h := Scheme.IdealSheafData.comap_mono T.map hHI
    change H.comap T.map ≤ I.comap T.map at h
    rw [T.hypersurface, hL] at h
    exact (Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff _ _).mp h
  constructor
  · rw [GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction.baseMap, Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp I T.coefficientMap H.subschemeι,
      T.coefficient_over, Scheme.IdealSheafData.comap_comp, hL,
      Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  · rw [EtaleLine.RetractionStep.Construction.etaleLineCenter_eq, EtaleLine.NormalDerivation.Construction.etaleLineCoefficientMap_eq, ← A.normal_eq,
      HypersurfaceCenters.Construction.retracted_hypersurface_center_comap T.normal A.retraction K, ← Ideal.comap_comap]
    change (((L.map (Ideal.Quotient.mk (Ideal.span {T.normal}))).map A.retraction.toRingHom).comap
      A.retraction.toRingHom).comap (Ideal.Quotient.mk (Ideal.span {T.normal})) = L
    rw [Ideal.comap_map_of_bijective A.retraction.toRingHom A.retraction.bijective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hnormal]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Retracted
