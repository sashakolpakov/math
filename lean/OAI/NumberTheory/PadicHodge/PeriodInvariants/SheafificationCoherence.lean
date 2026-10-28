import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence

/-! # Sheafification Coherence -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafificationCoherence

noncomputable section

/-!
# Coherence of sheafification under exact restriction

The comparison with sheafification is characterized by its action on the
original presheaf. This gives identity and composition laws for arbitrary
presheaves, including the crystalline structure presheaf.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor

variable {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
variable [HasWeakSheafify J A] [HasWeakSheafify K A] [HasWeakSheafify L A]
variable (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]

def transport (P : Dᵒᵖ ⥤ A) :
    (F.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj P) ≅
      (presheafToSheaf J A).obj (F.op ⋙ P) :=
  (F.pushforwardContinuousSheafificationCompatibility A J K).symm.app P

theorem transport_generator (P : Dᵒᵖ ⥤ A) :
    toSheafify J (F.op ⋙ P) ≫ (transport J K F P).inv.hom =
      whiskerLeft F.op (toSheafify K P) :=
  F.toSheafify_pullbackSheafificationCompatibility A J K P

def transported (P : Dᵒᵖ ⥤ A) (Q : Cᵒᵖ ⥤ A) (e : F.op ⋙ P ≅ Q) :
    (F.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj P) ≅
      (presheafToSheaf J A).obj Q :=
  transport J K F P ≪≫ (presheafToSheaf J A).mapIso e

theorem transported_generator (P : Dᵒᵖ ⥤ A) (Q : Cᵒᵖ ⥤ A) (e : F.op ⋙ P ≅ Q) :
    toSheafify J Q ≫ (transported J K F P Q e).inv.hom =
      e.inv ≫ whiskerLeft F.op (toSheafify K P) := by
  change toSheafify J Q ≫ (sheafifyMap J e.inv ≫ (transport J K F P).inv.hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (transport J K F P).inv.hom) (toSheafify_naturality J e.inv).symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => e.inv ≫ z) (transport_generator J K F P))))

theorem transport_hom_generator (P : Dᵒᵖ ⥤ A) :
    whiskerLeft F.op (toSheafify K P) ≫ (transport J K F P).hom.hom =
      toSheafify J (F.op ⋙ P) := by
  let e := (sheafToPresheaf J A).mapIso (transport J K F P)
  exact (congrArg (fun z => z ≫ e.hom) (transport_generator J K F P)).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => toSheafify J (F.op ⋙ P) ≫ z) e.inv_hom_id).trans (Category.comp_id _)))

section Identity

variable [∀ P : Cᵒᵖ ⥤ A, (𝟭 C).op.HasPointwiseRightKanExtension P]

omit K L [HasWeakSheafify K A] [HasWeakSheafify L A] F
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P] in
theorem transport_id (P : Cᵒᵖ ⥤ A) : transport J J (𝟭 C) P = Iso.refl _ := by
  apply Iso.ext_inv
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ ((presheafToSheaf J A).obj P).property
  exact (transport_generator J J (𝟭 C) P).trans (Category.comp_id _).symm

end Identity

variable (G : D ⥤ E) [G.IsContinuous K L] [G.IsCocontinuous K L]
  [∀ P : Dᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A, (F ⋙ G).op.HasPointwiseRightKanExtension P]

theorem transport_comp (P : Eᵒᵖ ⥤ A) :
    letI := isContinuous_comp F G J K L
    letI := isCocontinuous_comp F G J K (L := L)
    (F.sheafPushforwardContinuous A J K).mapIso (transport K L G P) ≪≫
        transport J K F (G.op ⋙ P) = transport J L (F ⋙ G) P := by
  let := isContinuous_comp F G J K L
  let := isCocontinuous_comp F G J K (L := L)
  apply Iso.ext_inv
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    ((F.sheafPushforwardContinuous A J K).obj
      ((G.sheafPushforwardContinuous A K L).obj ((presheafToSheaf L A).obj P))).property
  change toSheafify J ((F ⋙ G).op ⋙ P) ≫
      ((transport J K F (G.op ⋙ P)).inv.hom ≫ whiskerLeft F.op (transport K L G P).inv.hom) =
    toSheafify J ((F ⋙ G).op ⋙ P) ≫ (transport J L (F ⋙ G) P).inv.hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ whiskerLeft F.op (transport K L G P).inv.hom)
      (transport_generator J K F (G.op ⋙ P))).trans
      ((whiskerLeft_comp F.op (toSheafify K (G.op ⋙ P)) (transport K L G P).inv.hom).symm.trans
        ((congrArg (whiskerLeft F.op) (transport_generator K L G P)).trans
          (transport_generator J L (F ⋙ G) P).symm)))

section Naturality

variable {F' : C ⥤ D} [F'.IsContinuous J K] [F'.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F'.op.HasPointwiseRightKanExtension P]

omit L [HasWeakSheafify L A] G [G.IsContinuous K L] [G.IsCocontinuous K L]
  [∀ P : Dᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A, (F ⋙ G).op.HasPointwiseRightKanExtension P] in
theorem transport_natIso (e : F ≅ F') (P : Dᵒᵖ ⥤ A) :
    transport J K F P =
      (Functor.sheafPushforwardContinuousIso e A J K).app ((presheafToSheaf K A).obj P) ≪≫
        transport J K F' P ≪≫ (presheafToSheaf J A).mapIso (isoWhiskerRight (NatIso.op e) P) := by
  let c := (Functor.sheafPushforwardContinuousIso e A J K).app ((presheafToSheaf K A).obj P)
  have hn : (isoWhiskerRight (NatIso.op e) P).inv ≫ whiskerLeft F'.op (toSheafify K P) =
      whiskerLeft F.op (toSheafify K P) ≫ c.hom.hom := by
    apply NatTrans.ext
    funext U
    exact (toSheafify K P).naturality (e.inv.app U.unop).op
  apply Iso.ext_inv
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    ((F.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj P)).property
  change toSheafify J (F.op ⋙ P) ≫ (transport J K F P).inv.hom =
    toSheafify J (F.op ⋙ P) ≫
      ((sheafifyMap J (isoWhiskerRight (NatIso.op e) P).inv ≫ (transport J K F' P).inv.hom) ≫ c.inv.hom)
  simp only [Category.assoc]
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    ← Category.assoc (toSheafify J (F'.op ⋙ P)), transport_generator J K F' P]
  have hc : c.hom.hom ≫ c.inv.hom = 𝟙 _ :=
    (sheafToPresheaf J A).mapIso c |>.hom_inv_id
  exact (transport_generator J K F P).trans
    (((Category.assoc (isoWhiskerRight (NatIso.op e) P).inv
      (whiskerLeft F'.op (toSheafify K P)) c.inv.hom).symm.trans
      ((congrArg (fun z => z ≫ c.inv.hom) hn).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => whiskerLeft F.op (toSheafify K P) ≫ z) hc).trans
            (Category.comp_id _))))).symm)

end Naturality

variable (F₀ : C ⥤ C) [F₀.IsContinuous J J] [F₀.IsCocontinuous J J]
  [∀ P : Cᵒᵖ ⥤ A, F₀.op.HasPointwiseRightKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A, (𝟭 C).op.HasPointwiseRightKanExtension P]

theorem transport_idIso (e : F₀ ≅ 𝟭 C) (P : Cᵒᵖ ⥤ A) :
    transport J J F₀ P ≪≫
        ((presheafToSheaf J A).mapIso (isoWhiskerRight (NatIso.op e) P)).symm =
      (Functor.sheafPushforwardContinuousIso e A J J).app ((presheafToSheaf J A).obj P) := by
  let c := (Functor.sheafPushforwardContinuousIso e A J J).app ((presheafToSheaf J A).obj P)
  let q := (presheafToSheaf J A).mapIso (isoWhiskerRight (NatIso.op e) P)
  have hi : transport J J (𝟭 C) P = Iso.refl ((presheafToSheaf J A).obj P) := transport_id J P
  have ht := (congrArg (fun i : (presheafToSheaf J A).obj P ≅ (presheafToSheaf J A).obj P =>
    c ≪≫ i ≪≫ q) hi).trans (congrArg (fun i => c ≪≫ i) (Iso.refl_trans q))
  have h := (transport_natIso J J F₀ e P).trans ht
  exact (congrArg (fun i => i ≪≫ q.symm) h).trans
    ((Iso.trans_assoc c q q.symm).trans
      ((congrArg (fun i => c ≪≫ i) (Iso.self_symm_id q)).trans (Iso.trans_refl c)))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafificationCoherence
