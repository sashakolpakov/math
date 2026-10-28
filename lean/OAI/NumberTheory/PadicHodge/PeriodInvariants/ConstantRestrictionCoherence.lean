import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence

/-! # Constant Restriction Coherence -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence

noncomputable section

/-!
# Coherence of constant sheaves under exact restriction

The canonical sheafification comparison preserves constant generators.
This proves its identity, composition, and natural-isomorphism laws,
for arbitrary continuous and cocontinuous functors of sites.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor Opposite

open OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence

variable {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
variable [HasWeakSheafify J A] [HasWeakSheafify K A] [HasWeakSheafify L A]
variable (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]

def transport (a : A) :
    (F.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj a) ≅
      (constantSheaf J A).obj a :=
  (F.pushforwardContinuousSheafificationCompatibility A J K).symm.app
    ((Functor.const _).obj a)

theorem transport_generator (a : A) :
    ConstantSheafCoherence.constantGenerator J a ≫ (transport J K F a).inv.hom =
      whiskerLeft F.op (ConstantSheafCoherence.constantGenerator K a) :=
  F.toSheafify_pullbackSheafificationCompatibility A J K ((Functor.const _).obj a)

theorem transport_hom_generator (a : A) :
    whiskerLeft F.op (ConstantSheafCoherence.constantGenerator K a) ≫ (transport J K F a).hom.hom =
      ConstantSheafCoherence.constantGenerator J a := by
  let c := (sheafToPresheaf J A).mapIso (transport J K F a)
  have hc : c.inv ≫ c.hom = 𝟙 _ := c.inv_hom_id
  exact (congrArg (fun z => z ≫ c.hom) (transport_generator J K F a)).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => ConstantSheafCoherence.constantGenerator J a ≫ z) hc).trans (Category.comp_id _)))

section Identity

variable [∀ P : Cᵒᵖ ⥤ A, (𝟭 C).op.HasPointwiseRightKanExtension P]

omit K L [HasWeakSheafify K A] [HasWeakSheafify L A] F
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P] in
theorem transport_id (a : A) : transport J J (𝟭 C) a = Iso.refl _ := by
  apply Iso.ext_inv
  apply ConstantSheafCoherence.constant_hom_ext J
  exact (transport_generator J J (𝟭 C) a).trans (Category.comp_id _).symm

end Identity

variable (G : D ⥤ E) [G.IsContinuous K L] [G.IsCocontinuous K L]
  [∀ P : Dᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A, (F ⋙ G).op.HasPointwiseRightKanExtension P]

theorem transport_comp (a : A) :
    letI := isContinuous_comp F G J K L
    letI := isCocontinuous_comp F G J K (L := L)
    (F.sheafPushforwardContinuous A J K).mapIso (transport K L G a) ≪≫ transport J K F a =
      transport J L (F ⋙ G) a := by
  let := isContinuous_comp F G J K L
  let := isCocontinuous_comp F G J K (L := L)
  apply Iso.ext_inv
  apply ConstantSheafCoherence.constant_hom_ext J
  change ConstantSheafCoherence.constantGenerator J a ≫
      ((transport J K F a).inv.hom ≫ whiskerLeft F.op (transport K L G a).inv.hom) =
    ConstantSheafCoherence.constantGenerator J a ≫ (transport J L (F ⋙ G) a).inv.hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ whiskerLeft F.op (transport K L G a).inv.hom)
      (transport_generator J K F a)).trans
      ((whiskerLeft_comp F.op (ConstantSheafCoherence.constantGenerator K a) (transport K L G a).inv.hom).symm.trans
        ((congrArg (whiskerLeft F.op) (transport_generator K L G a)).trans
          (transport_generator J L (F ⋙ G) a).symm)))

variable {F' : C ⥤ D} [F'.IsContinuous J K] [F'.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F'.op.HasPointwiseRightKanExtension P]

omit L [HasWeakSheafify L A] G [G.IsContinuous K L] [G.IsCocontinuous K L]
  [∀ P : Dᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A, (F ⋙ G).op.HasPointwiseRightKanExtension P] in
theorem transport_natIso (e : F ≅ F') (a : A) :
    transport J K F a =
      (Functor.sheafPushforwardContinuousIso e A J K).app ((constantSheaf K A).obj a) ≪≫
        transport J K F' a := by
  apply Iso.ext_inv
  apply ConstantSheafCoherence.constant_hom_ext J
  change ConstantSheafCoherence.constantGenerator J a ≫ (transport J K F a).inv.hom =
    ConstantSheafCoherence.constantGenerator J a ≫ ((transport J K F' a).inv.hom ≫
      ((Functor.sheafPushforwardContinuousIso e A J K).inv.app ((constantSheaf K A).obj a)).hom)
  rw [← Category.assoc, transport_generator, transport_generator]
  apply NatTrans.ext
  funext U
  exact (ConstantSheafCoherence.constantGenerator_naturality K a (e.hom.app U.unop).op).symm

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence
