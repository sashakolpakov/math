import OAI.AlgebraicGeometry.Resolution.Blowups.SymmetricCoordinateFirstCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.SymmetricPrefixIsoTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.EtalePullbackExistence

/-! # Symmetric Coordinate Model Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The first-center classification is intrinsic under any isomorphic presentation by a coordinate model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleSymmetric.first_center_of_coordinate_model
    {σ τ : Type} [Fintype σ] [Fintype τ]
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (C : X.IdealSheafData) (hC : C ≠ ⊥) (hp : J ≤ C ^ 1)
    (hs : Smooth (C.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J hC 1) Y g K)
    (H : (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup C hC (by decide) hp hs hbl tail).EtaleSymmetric)
    (q : Spec (.of (MvPolynomial (σ ⊕ τ) ℂ)) ⟶ X) [IsIso q]
    (hf : q ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (MvPolynomial (σ ⊕ τ) ℂ))
    (hJ : J.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel (RingHom.ker Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom)) :
    C = J ∨ C = ⊤ := by
  let P := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup C hC (by decide) hp hs hbl tail
  obtain ⟨W, k, M, Q, r, hc⟩ := P.exists_etale_pullback _
    (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (MvPolynomial (σ ⊕ τ) ℂ))
    (Affine.QuotientKernel.Construction.affineQuotientKernel (RingHom.ker Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom)) q hf hJ
  have HQ := H.of_isomorphic_comparison P Q q r hc hf hJ
  obtain ⟨hV, hNV, B, hB, hb, hpB, hsB, hblB, rest, heQ⟩ :=
    hc.exists_blowup C hC (by decide) hp hs hbl tail Q q r
  let : IsIntegral (Spec (.of (MvPolynomial (σ ⊕ τ) ℂ))) := hV
  let : IsLocallyNoetherian (Spec (.of (MvPolynomial (σ ⊕ τ) ℂ))) := hNV
  subst Q
  obtain ⟨_, _, _, he, _⟩ := (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff
    C hC (by decide) hp hs hbl tail B hB hb hpB hsB hblB rest q r).mp hc
  rcases HQ.coordinate_first_center_eq_or_top B hB hpB hsB hblB rest with h | h
  · left
    have heq : C.comap q = J.comap q := he.trans (h.trans hJ.symm)
    exact le_antisymm ((Affine.IdealChartDescent.Construction.idealSheaf_comap_le_iff_isIso _ _ q).mp heq.le)
      ((Affine.IdealChartDescent.Construction.idealSheaf_comap_le_iff_isIso _ _ q).mp heq.ge)
  · right
    have heq : C.comap q = (⊤ : X.IdealSheafData).comap q := by
      rw [he, h, Scheme.IdealSheafData.comap_top]
    exact le_antisymm le_top ((Affine.IdealChartDescent.Construction.idealSheaf_comap_le_iff_isIso _ _ q).mp heq.ge)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
