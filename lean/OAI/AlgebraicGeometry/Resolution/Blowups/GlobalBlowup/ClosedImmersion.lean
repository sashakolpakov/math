import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.FunctorialMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ClosedMap

/-! # Closed Immersion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.ClosedImmersion.Construction

noncomputable section

/-! The actual blowup of a closed integral carrier embeds in the ambient blowup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [IsIntegral Y] [IsLocallyNoetherian Y]

/-- On inverse images of affine base opens, the global comparison is precisely
the closed affine Rees map. -/
theorem globalBlowupMap_affine_isPullback (q : Y ⟶ X) [IsAffineHom q]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥) (U : X.affineOpens) :
    let V : Y.affineOpens := ⟨q ⁻¹ᵁ U.1, U.2.preimage q⟩
    IsPullback
      (Blowup.Functor.Construction.affineBlowupMapTo (I.ideal U) ((I.comap q).ideal V) (q.appLE U.1 V.1 le_rfl).hom
        (IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I q U V le_rfl).symm)
      (Data.Construction.globalBlowupChart (I.comap q) hY V)
      (Data.Construction.globalBlowupChart I hI U) (FunctorialMap.Construction.globalBlowupMap q I hI hY) := by
  dsimp only
  apply IsOpenImmersion.isPullback
  · exact FunctorialMap.Construction.globalBlowupMap_chart q I hI hY U ⟨q ⁻¹ᵁ U.1, U.2.preimage q⟩ le_rfl
  · rw [MapGluing.Construction.globalBlowupChart_opensRange, MapGluing.Construction.globalBlowupChart_opensRange,
      ← Scheme.Hom.comp_preimage, FunctorialMap.Construction.globalBlowupMap_over, Scheme.Hom.comp_preimage]

/-- The blowup of the pulled-back nonzero center on a closed integral carrier
is a closed subscheme of the actual ambient blowup. -/
theorem globalBlowupMap_isClosedImmersion (q : Y ⟶ X) [IsClosedImmersion q]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥) :
    IsClosedImmersion (FunctorialMap.Construction.globalBlowupMap q I hI hY) := by
  let C := MapGluing.Construction.globalBlowupChosenCover I hI (fun U : X.affineOpens => U)
    (iSup_affineOpens_eq_top X)
  apply IsZariskiLocalAtTarget.of_openCover C
  intro U
  change X.affineOpens at U
  let V : Y.affineOpens := ⟨q ⁻¹ᵁ U.1, U.2.preimage q⟩
  let φ := (q.appLE U.1 V.1 le_rfl).hom
  have hφ : Function.Surjective φ := by
    change Function.Surjective (q.appLE U.1 (q ⁻¹ᵁ U.1) le_rfl).hom
    rw [Scheme.Hom.appLE_eq_app]
    exact q.app_surjective U.1 U.2
  let : IsClosedImmersion (Blowup.Functor.Construction.affineBlowupMapTo (I.ideal U) ((I.comap q).ideal V) φ
      (IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I q U V le_rfl).symm) :=
    Blowup.ClosedMap.Construction.affineBlowupMapTo_isClosedImmersion _ _ _ _ hφ
  change IsClosedImmersion (pullback.snd (FunctorialMap.Construction.globalBlowupMap q I hI hY)
    (Data.Construction.globalBlowupChart I hI U))
  rw [← (globalBlowupMap_affine_isPullback q I hI hY U).flip.isoPullback_inv_snd]
  infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.ClosedImmersion.Construction
