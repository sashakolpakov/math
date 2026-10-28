import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.GlobalOpenComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterPrincipalEquations
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.AtlasFromAffineCover
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterComposition

/-! # Pointed Center Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A globally constant incidence set remains fixed on any pointed étale affine restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.exists_uniform_pointed_restriction
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (F : Finset β) (hF : ∀ i, A.divided i = F)
    (R : CommRingCat) [Algebra ℂ R] (j : Spec R ⟶ X) [Etale j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (K : Ideal R) (w : β → R)
    (hK : I.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K)
    (hw : ∀ l, (D l).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w l}))
    (p : PrimeSpectrum R) (hp : K ≤ p.asIdeal) :
    Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart ℂ R K w F p) := by
  obtain ⟨i, q, hq⟩ := Global.MonomialBoundaryAtlas.Construction.exists_point_on_chosen_affine_spec A.opens A.cover (j p)
  let U := A.opens i
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  obtain ⟨S, hSk, φ, ψ, hφ, hψ, hcomm, P, hP, _⟩ :=
    Pointed.GlobalOpenComparison.Construction.exists_pointed_global_open_comparison f R (.of Γ(X, U)) j U.2.fromSpec hj
      (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U).symm p q hq.symm
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := hφ
  have hIU : I.comap U.2.fromSpec = Affine.QuotientKernel.Construction.affineQuotientKernel (I.ideal U) :=
    Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel I U
  have hcenter : K.map φ.toRingHom = (I.ideal U).map ψ.toRingHom := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    rw [← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom,
      ← hK, ← hIU,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomm]
  have hboundary (l : β) : Ideal.span {ψ (A.equations i l)} = Ideal.span {φ (w l)} := by
    have hDU : (D l).comap U.2.fromSpec = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {A.equations i l}) := by
      exact (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel (D l) U).trans
        (congrArg Affine.QuotientKernel.Construction.affineQuotientKernel (A.component i l))
    have he : (Ideal.span {w l}).map φ.toRingHom =
        (Ideal.span {A.equations i l}).map ψ.toRingHom := by
      apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
      rw [← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← hw l,
        ← hDU,
        ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomm]
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at he
    convert he.symm using 1
  have hc : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts ℂ S (K.map φ.toRingHom)
      (fun l => φ (w l)) (A.divided i) := by
    rw [hcenter]
    exact ((A.center i).etale_baseChange ψ hψ).replacePrincipalEquations
      (fun l => φ (w l)) hboundary
  have hKP : K.map φ.toRingHom ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    have he : P.asIdeal.comap φ.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hP
    rw [he]
    exact hp
  obtain ⟨C⟩ := hc P hKP
  rw [← hF i]
  exact ⟨C.comp K w (A.divided i) φ p hP⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
