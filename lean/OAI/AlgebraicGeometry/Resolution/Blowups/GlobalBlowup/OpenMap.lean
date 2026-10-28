import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Equivalence
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapGluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Open Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenMap.Construction

noncomputable section

/-! The actual global Rees blowup map induced by an open immersion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {V X : Scheme} (j : V ⟶ X) [IsOpenImmersion j]

abbrev openImageAffine (U : V.affineOpens) : X.affineOpens :=
  ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩

abbrev openImageSectionEquiv (U : V.affineOpens) :
    Γ(X, openImageAffine j U) ≃+* Γ(V, U) :=
  (j.appIso U.1).commRingCatIsoToRingEquiv

theorem openImageSectionEquiv_ideal (I : X.IdealSheafData) (U : V.affineOpens) :
    (I.ideal (openImageAffine j U)).map (openImageSectionEquiv j U).toRingHom =
      (I.comap j).ideal U := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact Ideal.map_comap_of_equiv (openImageSectionEquiv j U)

theorem openImageSectionEquiv_over (U : V.affineOpens) :
    Spec.map (CommRingCat.ofHom (openImageSectionEquiv j U).toRingHom) ≫
        (openImageAffine j U).2.fromSpec = U.2.fromSpec ≫ j := by
  change Spec.map (j.appIso U.1).hom ≫ _ = _
  rw [Scheme.Hom.appIso_hom']
  exact IsAffineOpen.SpecMap_appLE_fromSpec j _ U.2 _

theorem openImageSectionEquiv_naturality {U W : V.affineOpens} (h : U ≤ W) :
    (openImageSectionEquiv j U).toRingHom.comp
        (Blowup.Functor.Construction.affineRestriction (show openImageAffine j U ≤ openImageAffine j W from
          Set.image_mono h)) =
      (Blowup.Functor.Construction.affineRestriction h).comp (openImageSectionEquiv j W).toRingHom := by
  exact congrArg CommRingCat.Hom.hom (j.appIso_hom_naturality
    (homOfLE (X := V.Opens) h).op)

variable [IsIntegral X] [IsLocallyNoetherian X]

def globalBlowupOpenChart (I : X.IdealSheafData) (hI : I ≠ ⊥) (U : V.affineOpens) :
    ReesGrading.Construction.affineBlowup ((I.comap j).ideal U) ⟶ Data.Construction.globalBlowup I hI :=
  Blowup.Functor.Construction.affineBlowupMapTo (I.ideal (openImageAffine j U)) ((I.comap j).ideal U)
    (openImageSectionEquiv j U).toRingHom (openImageSectionEquiv_ideal j I U) ≫
      Data.Construction.globalBlowupChart I hI (openImageAffine j U)

instance globalBlowupOpenChart_isOpenImmersion
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (U : V.affineOpens) :
    IsOpenImmersion (globalBlowupOpenChart j I hI U) := by
  let : IsIso (Blowup.Functor.Construction.affineBlowupMapTo (I.ideal (openImageAffine j U)) ((I.comap j).ideal U)
    (openImageSectionEquiv j U).toRingHom (openImageSectionEquiv_ideal j I U)) :=
    Blowup.Equivalence.Construction.affineBlowupMapTo_isIso_of_equiv _ _ _ _
  unfold globalBlowupOpenChart
  infer_instance

theorem globalBlowupOpenChart_over
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (U : V.affineOpens) :
    globalBlowupOpenChart j I hI U ≫ Data.Construction.globalBlowupToBase I hI =
      ReesGrading.Construction.affineBlowupToSpec ((I.comap j).ideal U) ≫ U.2.fromSpec ≫ j := by
  unfold globalBlowupOpenChart
  rw [Category.assoc, Data.Construction.globalBlowupChart_over, ← Category.assoc, Blowup.Functor.Construction.affineBlowupMapTo_over,
    Category.assoc, openImageSectionEquiv_over]

theorem globalBlowupOpenChart_transition
    (I : X.IdealSheafData) (hI : I ≠ ⊥) {U W : V.affineOpens} (h : U ≤ W) :
    (Blowup.Functor.Construction.idealBlowupFunctor (I.comap j)).map (homOfLE h) ≫ globalBlowupOpenChart j I hI W =
      globalBlowupOpenChart j I hI U := by
  have him : openImageAffine j U ≤ openImageAffine j W := Set.image_mono h
  have he := openImageSectionEquiv_naturality j h
  have hleft :
      (I.ideal (openImageAffine j W)).map
        ((Blowup.Functor.Construction.affineRestriction h).comp (openImageSectionEquiv j W).toRingHom) =
        (I.comap j).ideal U := by
    rw [← Ideal.map_map, openImageSectionEquiv_ideal, Blowup.Functor.Construction.affineRestriction_ideal]
  have hright :
      (I.ideal (openImageAffine j W)).map
        ((openImageSectionEquiv j U).toRingHom.comp (Blowup.Functor.Construction.affineRestriction him)) =
        (I.comap j).ideal U := by rw [he]; exact hleft
  change (Blowup.Functor.Construction.affineBlowupMapTo _ _ (Blowup.Functor.Construction.affineRestriction h) _ ≫
      (Blowup.Functor.Construction.affineBlowupMapTo _ _ (openImageSectionEquiv j W).toRingHom _ ≫ _)) = _
  rw [← Category.assoc, ← Blowup.Functor.Construction.affineBlowupMapTo_comp _ _ _ _ _ _ _ hleft]
  simp only [← he]
  rw [Blowup.Functor.Construction.affineBlowupMapTo_comp _ _ _ _ _ (Blowup.Functor.Construction.affineRestriction_ideal I him)
    (openImageSectionEquiv_ideal j I U) hright, Category.assoc]
  change Blowup.Functor.Construction.affineBlowupMapTo _ _ _ _ ≫
    ((Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE him) ≫ Data.Construction.globalBlowupChart I hI _) = _
  exact congrArg (fun g => Blowup.Functor.Construction.affineBlowupMapTo (I.ideal (openImageAffine j U))
    ((I.comap j).ideal U) (openImageSectionEquiv j U).toRingHom
    (openImageSectionEquiv_ideal j I U) ≫ g) (Data.Construction.globalBlowupChart_transition I hI him)

def globalBlowupOpenCocone (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    Cocone (Blowup.Functor.Construction.idealBlowupFunctor (I.comap j)) where
  pt := Data.Construction.globalBlowup I hI
  ι := {
    app := globalBlowupOpenChart j I hI
    naturality := by
      intro U W h
      exact (globalBlowupOpenChart_transition j I hI (leOfHom h)).trans
        (Category.comp_id _).symm }

variable [IsIntegral V] [IsLocallyNoetherian V]

def globalBlowupOpenMap (I : X.IdealSheafData) (hI : I ≠ ⊥) (hV : I.comap j ≠ ⊥) :
    Data.Construction.globalBlowup (I.comap j) hV ⟶ Data.Construction.globalBlowup I hI :=
  colimit.desc (Data.Construction.blowupGluingData (I.comap j) hV).functor (globalBlowupOpenCocone j I hI)

theorem globalBlowupOpenMap_chart (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (hV : I.comap j ≠ ⊥) (U : V.affineOpens) :
    Data.Construction.globalBlowupChart (I.comap j) hV U ≫ globalBlowupOpenMap j I hI hV =
      globalBlowupOpenChart j I hI U :=
  colimit.ι_desc (F := (Data.Construction.blowupGluingData (I.comap j) hV).functor)
    (globalBlowupOpenCocone j I hI) U

theorem globalBlowupOpenMap_over (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (hV : I.comap j ≠ ⊥) :
    globalBlowupOpenMap j I hI hV ≫ Data.Construction.globalBlowupToBase I hI =
      Data.Construction.globalBlowupToBase (I.comap j) hV ≫ j := by
  apply colimit.hom_ext
  intro U
  change V.affineOpens at U
  change Data.Construction.globalBlowupChart (I.comap j) hV U ≫ _ =
    Data.Construction.globalBlowupChart (I.comap j) hV U ≫ _
  rw [← Category.assoc, globalBlowupOpenMap_chart, globalBlowupOpenChart_over]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ j) (Data.Construction.globalBlowupChart_over (I.comap j) hV U).symm).trans
      (Category.assoc _ _ _))

instance globalBlowupOpenMap_isOpenImmersion (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (hV : I.comap j ≠ ⊥) : IsOpenImmersion (globalBlowupOpenMap j I hI hV) := by
  apply Blowup.BlowupRestriction.Construction.isOpenImmersion_of_local_base_charts (globalBlowupOpenMap j I hI hV)
    (Data.Construction.globalBlowupToBase I hI) (Data.Construction.globalBlowupToBase (I.comap j) hV) j
    (globalBlowupOpenMap_over j I hI hV)
  intro y
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := y) trivial
  let W : V.affineOpens := ⟨U, hU⟩
  refine ⟨ReesGrading.Construction.affineBlowup ((I.comap j).ideal W), W.1,
    Data.Construction.globalBlowupChart (I.comap j) hV W,
    ReesGrading.Construction.affineBlowupToSpec ((I.comap j).ideal W) ≫ W.2.isoSpec.inv, W.1.ι,
    inferInstance, Data.Construction.globalBlowup_affineOpen_isPullback (I.comap j) hV W,
    ⟨⟨y, hy⟩, rfl⟩, ?_⟩
  rw [globalBlowupOpenMap_chart]
  infer_instance

theorem globalBlowupOpenMap_isPullback (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (hV : I.comap j ≠ ⊥) :
    IsPullback (globalBlowupOpenMap j I hI hV) (Data.Construction.globalBlowupToBase (I.comap j) hV)
      (Data.Construction.globalBlowupToBase I hI) j :=
  Blowup.BaseChange.Construction.isPullback_of_proper_open_diagram (Data.Construction.globalBlowupToBase I hI) j
    (Data.Construction.globalBlowupToBase (I.comap j) hV) (globalBlowupOpenMap j I hI hV)
    (globalBlowupOpenMap_over j I hI hV)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenMap.Construction
