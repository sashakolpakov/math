import OAI.AlgebraicGeometry.Resolution.Blowups.Global.UniformIncidenceTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CanonicalBoundaryComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Center
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.EmbeddingIso

/-! # Canonical Boundary Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! An exact common incidence set gives canonical boundary comparison even when a smooth center is disconnected. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.uniform_boundary_le_center
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (F : Finset β) (hF : ∀ i, A.divided i = F) (j : β) (hj : j ∈ F) : D j ≤ I := by
  apply GlobalComponent.Center.Construction.idealSheaf_le_of_native_affine_cover A.opens A.cover
  intro i
  rw [A.component i j]
  apply Ideal.span_le.mpr
  rintro _ rfl
  exact A.contained i j ((hF i).symm ▸ hj)

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.uniform_canonical_eq_mixed
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {I : X.IdealSheafData} {β : Type} {D : β → X.IdealSheafData}
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (F : Finset β) (hF : ∀ i, A.divided i = F) (hI : I ≠ ⊥) :
    CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D = Global.MixedBoundary.Construction.globalBlowupMixedBoundary I hI D F := by
  let B := A.withUniformIncidence F (fun i _ => hF i)
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
      (Global.MixedBoundary.Construction.globalBlowupMixedBoundary_comap_reesChart I hI D (B.divided p.1) (B.opens p.1)
        (B.equations p.1) (B.component p.1) (B.contained p.1) p.2 j).symm

theorem Uniform.CanonicalBoundaryComparison.Construction.globalBlowupMapTo_uniform_canonicalBoundary
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (q : Y ⟶ X) (I : X.IdealSheafData) (K : Y.IdealSheafData)
    (he : I.comap q = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥)
    {β : Type} (D : β → X.IdealSheafData) (F : Finset β)
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (hA : ∀ i, A.divided i = F)
    (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (q ≫ f) K (fun j => (D j).comap q)) (hB : ∀ i, B.divided i = F)
    (j : Option β) :
    (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D j).comap (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K he hI hK) =
      CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary K hK (fun j => (D j).comap q) j := by
  rw [A.uniform_canonical_eq_mixed F hA hI, B.uniform_canonical_eq_mixed F hB hK]
  exact GlobalBlowup.BoundaryComparison.Construction.globalBlowupMapTo_mixedBoundary q I K he hI hK D F (A.uniform_boundary_le_center F hA) j

theorem Uniform.CanonicalBoundaryComparison.Construction.carrier_blowup_embedding_iso_uniform_canonicalBoundary
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I H : X.IdealSheafData) (hI : I ≠ ⊥)
    [IsIntegral H.subscheme] [IsLocallyNoetherian H.subscheme]
    (K : H.subscheme.IdealSheafData) (hK : K ≠ ⊥) (hIK : I.comap H.subschemeι = K)
    (e : GlobalBlowup.Data.Construction.globalBlowup K hK ≅ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme)
    (he : e.hom ≫ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι = GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo H.subschemeι I K hIK hI hK)
    {β : Type} (D : β → X.IdealSheafData) (F : Finset β)
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (hA : ∀ i, A.divided i = F)
    (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (H.subschemeι ≫ f) K (fun j => (D j).comap H.subschemeι))
    (hB : ∀ i, B.divided i = F) (j : Option β) :
    ((CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D j).comap (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι).comap e.hom =
      CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary K hK (fun j => (D j).comap H.subschemeι) j := by
  rw [← Scheme.IdealSheafData.comap_comp, he]
  exact Uniform.CanonicalBoundaryComparison.Construction.globalBlowupMapTo_uniform_canonicalBoundary f H.subschemeι I K hIK hI hK D F A hA B hB j

end

end OAI.AlgebraicGeometry.Resolution.Blowups
