import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.BoundaryComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.SchemeImage

/-! # Canonical Boundary Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Canonical full boundary families agree under compatible integral closed-carrier blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem CanonicalBoundaryComparison.Construction.closedCarrierCenter_isIntegral {X Y : Scheme} (q : Y ⟶ X) [IsClosedImmersion q]
    (K : Y.IdealSheafData) [IsIntegral K.subscheme] : IsIntegral (K.map q).subscheme :=
  Integral.SchemeImage.Construction.scheme_image_isIntegral (K.subschemeι ≫ q)

theorem CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.integral_canonical_eq_mixed
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {I : X.IdealSheafData} [IsIntegral I.subscheme] {β : Type} [Fintype β]
    {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (hI : I ≠ ⊥) :
    CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D =
      MixedBoundary.Construction.globalBlowupMixedBoundary I hI D (AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels I D) := by
  let B := A.uniformIncidence
  let Q := B.reesCover hI
  funext j
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ Q.openCover
  intro p
  let : Algebra ℂ Γ(X, B.opens p.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (B.opens p.1)
  have hb := MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup (.of Γ(X, B.opens p.1))
    (I.ideal (B.opens p.1)) (B.equations p.1) (B.divided p.1) (B.contained p.1)
    (B.boundary p.1) (B.center p.1) p.2
  exact (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary_comap_reesChart I hI D (B.divided p.1) (B.opens p.1)
    (B.equations p.1) (B.component p.1) (B.contained p.1) p.2 hb j).trans
      (MixedBoundary.Construction.globalBlowupMixedBoundary_comap_reesChart I hI D (B.divided p.1) (B.opens p.1)
        (B.equations p.1) (B.component p.1) (B.contained p.1) p.2 j).symm

theorem CanonicalBoundaryComparison.Construction.globalBlowup_closedCarrier_canonicalBoundary
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (q : Y ⟶ X) [IsClosedImmersion q]
    (K : Y.IdealSheafData) (hK : K ≠ ⊥) [IsIntegral K.subscheme]
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (K.map q) D)
    (B : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (q ≫ f) K (fun j => (D j).comap q)) (j : Option β) :
    (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (K.map q) (ClosedCarrierCenters.Construction.closedCarrierCenter_ne_bot q K hK) D j).comap
      (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q (K.map q) K (ClosedCarrierCenters.Construction.idealSheaf_closed_comap_map q K)
        (ClosedCarrierCenters.Construction.closedCarrierCenter_ne_bot q K hK) hK) =
      CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary K hK (fun j => (D j).comap q) j := by
  classical
  let : IsIntegral (K.map q).subscheme := CanonicalBoundaryComparison.Construction.closedCarrierCenter_isIntegral q K
  rw [A.integral_canonical_eq_mixed, B.integral_canonical_eq_mixed]
  rw [GlobalBlowup.BoundaryComparison.Construction.globalBlowupMapTo_mixedBoundary q (K.map q) K _ _ hK D _ (fun j hj => ?_),
    GlobalBlowup.BoundaryComparison.Construction.closedCarrierCenter_boundaryLabels]
  simpa only [AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hj

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
