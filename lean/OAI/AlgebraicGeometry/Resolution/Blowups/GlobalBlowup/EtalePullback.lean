import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtaleMap

/-! # Etale Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtalePullback.Construction

noncomputable section

/-! The global étale blowup comparison is the actual base-change square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem affineBlowupMapTo_flat_isPullback {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (φ : R →+* S) (h : I.map φ = J) (hφ : φ.Flat) :
    IsPullback (Blowup.Functor.Construction.affineBlowupMapTo I J φ h) (ReesGrading.Construction.affineBlowupToSpec J)
      (ReesGrading.Construction.affineBlowupToSpec I) (Spec.map (CommRingCat.ofHom φ)) := by
  subst J
  let : Algebra R S := φ.toAlgebra
  let : Module.Flat R S := hφ
  exact Blowup.FlatBaseChange.Construction.affineBlowup_flat_isPullback I

theorem globalBlowupMap_etale_isPullback
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ X) [Etale q]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥) :
    IsPullback (FunctorialMap.Construction.globalBlowupMap q I hI hY) (Data.Construction.globalBlowupToBase (I.comap q) hY)
      (Data.Construction.globalBlowupToBase I hI) q := by
  choose U V hsub hmem using IdealSheaf.ProductPullback.Construction.exists_affine_pair_at_point q
  have hcover : ⨆ y : Y, (V y).1 = ⊤ := by
    apply top_le_iff.mp
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hmem y⟩
  let C := (Global.MonomialBoundaryAtlas.Construction.chosenAffineSpecCover V hcover).openCover
  apply IsPullback.flip
  apply Scheme.isPullback_of_openCover _ _ _ _ C
  intro y
  change Y at y
  let φ := (q.appLE (U y).1 (V y).1 (hsub y)).hom
  have hφ : φ.Flat := (RingHom.Etale.iff_flat_and_formallyUnramified.mp
    (q.etale_appLE (U y).2 (V y).2 (hsub y))).1
  let a := Data.Construction.globalBlowupChart (I.comap q) hY (V y)
  let b := ReesGrading.Construction.affineBlowupToSpec ((I.comap q).ideal (V y))
  have hchart : IsPullback a b (Data.Construction.globalBlowupToBase (I.comap q) hY) (V y).2.fromSpec :=
    MapGluing.Construction.globalBlowup_affineSpec_isPullback (I.comap q) hY (V y)
  have houter : IsPullback (a ≫ FunctorialMap.Construction.globalBlowupMap q I hI hY) b
      (Data.Construction.globalBlowupToBase I hI) ((V y).2.fromSpec ≫ q) := by
    dsimp only [a, b]
    rw [FunctorialMap.Construction.globalBlowupMap_chart q I hI hY (U y) (V y) (hsub y)]
    have hs := ((affineBlowupMapTo_flat_isPullback (I.ideal (U y))
      ((I.comap q).ideal (V y)) φ
      (IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I q (U y) (V y) (hsub y)).symm hφ).flip.paste_vert
        (MapGluing.Construction.globalBlowup_affineSpec_isPullback I hI (U y)).flip).flip
    change IsPullback _ _ _ (Spec.map (q.appLE (U y).1 (V y).1 (hsub y)) ≫ (U y).2.fromSpec) at hs
    rwa [IsAffineOpen.SpecMap_appLE_fromSpec q (U y).2 (V y).2 (hsub y)] at hs
  change IsPullback
    (pullback.snd (Data.Construction.globalBlowupToBase (I.comap q) hY) (V y).2.fromSpec)
    (pullback.fst (Data.Construction.globalBlowupToBase (I.comap q) hY) (V y).2.fromSpec ≫ FunctorialMap.Construction.globalBlowupMap q I hI hY)
    ((V y).2.fromSpec ≫ q) (Data.Construction.globalBlowupToBase I hI)
  apply houter.flip.of_iso hchart.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    exact hchart.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (hchart.isoPullback_hom_fst_assoc _).symm
  · simp
  · simp

theorem globalBlowupMapTo_etale_isPullback
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ X) [Etale q]
    (I : X.IdealSheafData) (K : Y.IdealSheafData)
    (hq : I.comap q = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥) :
    IsPullback (SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK) (Data.Construction.globalBlowupToBase K hK)
      (Data.Construction.globalBlowupToBase I hI) q := by
  subst K
  exact globalBlowupMap_etale_isPullback q I hI hK

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtalePullback.Construction
