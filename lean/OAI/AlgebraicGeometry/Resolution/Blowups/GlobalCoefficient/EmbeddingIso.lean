import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Upper
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CanonicalBoundaryComparison

/-! # Embedding Iso -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.EmbeddingIso.Construction

noncomputable section

/-! Retain the actual closed-carrier embedding as well as coefficients under the blowup isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

local instance embeddingIsoCarrierNoetherian (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

theorem exists_globalRetainedCoefficientTransform_embedding_iso
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I)
    (K : H.subscheme.IdealSheafData) (hK : K ≠ ⊥) (hIK : I.comap H.subschemeι = K)
    (C : H.subscheme.IdealSheafData) (b : ℕ) :
    ∃ e : GlobalBlowup.Data.Construction.globalBlowup K hK ≅ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme,
      e.hom ≫ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι =
        GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo H.subschemeι I K hIK hI hK ∧
      e.hom ≫ ((GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)) =
        GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ (H.subschemeι ≫ f) ∧
      (Transform.Construction.globalRetainedCoefficientTransform I H C hI b).comap e.hom =
        GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K C hK b.factorial := by
  subst K
  obtain ⟨e, he, hover⟩ := Global.SmoothHypersurfaceBlowupIso.Construction.globalBlowup_smooth_hypersurface_iso f I H hI hH hlocal hHI hK
  have hr : e.hom ≫ Transform.Construction.globalControlledCarrierMap I H hI = GlobalBlowup.Data.Construction.globalBlowupToBase (I.comap H.subschemeι) hK := hover
  refine ⟨e, he, ?_, ?_⟩
  · have h := congrArg (fun v => v ≫ H.subschemeι ≫ f) hr
    rw [Category.assoc e.hom, ← Category.assoc (Transform.Construction.globalControlledCarrierMap I H hI) H.subschemeι f,
      Transform.Construction.globalControlledCarrierMap_over, Category.assoc] at h
    exact h
  · rw [Transform.Construction.globalRetainedCoefficientTransform, GlobalControlled.Ideal.Construction.controlledIdealSheaf_comap_open, hr]
    rfl

theorem carrier_blowup_embedding_iso_canonicalBoundary
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I H : X.IdealSheafData) (hI : I ≠ ⊥)
    [IsIntegral H.subscheme] (K : H.subscheme.IdealSheafData) (hK : K ≠ ⊥)
    [IsIntegral K.subscheme] (hIK : I.comap H.subschemeι = K) (hKI : K.map H.subschemeι = I)
    (e : GlobalBlowup.Data.Construction.globalBlowup K hK ≅ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme)
    (he : e.hom ≫ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι =
      GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo H.subschemeι I K hIK hI hK)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (H.subschemeι ≫ f) K (fun j => (D j).comap H.subschemeι))
    (j : Option β) :
    ((CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D j).comap
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι).comap e.hom =
      CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary K hK (fun j => (D j).comap H.subschemeι) j := by
  rw [← Scheme.IdealSheafData.comap_comp, he]
  subst I
  exact Global.CanonicalBoundaryComparison.Construction.globalBlowup_closedCarrier_canonicalBoundary f H.subschemeι K hK D A B j

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.EmbeddingIso.Construction
