import OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodInverseImage

/-! # Neighborhood Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodPairing

noncomputable section

/-!
# IntegralComparison: compatible maps on incidences describe neighborhood inverse-image morphisms
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Neighborhoods OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodColimit OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodRestriction

universe u v w u' v'

variable {C : Type u} [Category.{v} C] {A : Type w} [SemilatticeInf A]
  {D : Type u'} [Category.{v'} D] (P : A → ObjectProperty C)
  (hIncoming : ∀ V {T U : C}, (T ⟶ U) → P V U → P V T)
  (F : Aᵒᵖ ⥤ D) (G : Cᵒᵖ ⥤ D)

@[ext] structure Pairing where
  app (T : C) (V : Incoming.Neighborhoods.Objects P T) : F.obj (op V.obj) ⟶ G.obj (op T)
  neighborhood {T : C} {V W : Incoming.Neighborhoods.Objects P T} (α : V ⟶ W) :
    F.map ((Incoming.Neighborhoods.inclusion P T).map α).op ≫ app T V = app T W
  site {T U : C} (α : T ⟶ U) (V : Incoming.Neighborhoods.Objects P U) :
    app U V ≫ G.map α.op = app T ((Incoming.Neighborhoods.change P hIncoming α).obj V)

variable [∀ T, HasColimitsOfShape (Incoming.Neighborhoods.Objects P T)ᵒᵖ D]

def fromHom (η : NeighborhoodInverseImage.presheaf P hIncoming F ⟶ G) : Pairing P hIncoming F G where
  app T V := colimit.ι (NeighborhoodColimit.diagram P T F) (op V) ≫ η.app (op T)
  neighborhood := by
    intro T V W α
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫ η.app _) (colimit.w (NeighborhoodColimit.diagram P T F) α.op))
  site α V := (Category.assoc _ _ _).trans
    ((congrArg (fun a => colimit.ι (NeighborhoodColimit.diagram P _ F) (op V) ≫ a) (η.naturality α.op).symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ η.app _) (NeighborhoodRestriction.ι_restriction P hIncoming α F (op V)))))

def cocone (a : Pairing P hIncoming F G) (T : C) : Cocone (NeighborhoodColimit.diagram P T F) where
  pt := G.obj (op T)
  ι :=
    { app := fun V => a.app T V.unop
      naturality := fun _ _ α => (a.neighborhood α.unop).trans (Category.comp_id _).symm }

def desc (a : Pairing P hIncoming F G) (T : C) : colimit (NeighborhoodColimit.diagram P T F) ⟶ G.obj (op T) :=
  colimit.desc (NeighborhoodColimit.diagram P T F) (cocone P hIncoming F G a T)

theorem ι_desc (a : Pairing P hIncoming F G) (T : C) (V : (Incoming.Neighborhoods.Objects P T)ᵒᵖ) :
    colimit.ι (NeighborhoodColimit.diagram P T F) V ≫ NeighborhoodPairing.desc P hIncoming F G a T = a.app T V.unop :=
  colimit.ι_desc (cocone P hIncoming F G a T) V

def toHom (a : Pairing P hIncoming F G) : NeighborhoodInverseImage.presheaf P hIncoming F ⟶ G where
  app T := NeighborhoodPairing.desc P hIncoming F G a T.unop
  naturality T U α := by
    apply colimit.hom_ext
    intro V
    change colimit.ι (NeighborhoodColimit.diagram P T.unop F) V ≫ NeighborhoodRestriction.restriction P hIncoming α.unop F ≫ _ = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ NeighborhoodPairing.desc P hIncoming F G a U.unop)
        (NeighborhoodRestriction.ι_restriction P hIncoming α.unop F V)).trans
        ((NeighborhoodPairing.ι_desc P hIncoming F G a U.unop ((Incoming.Neighborhoods.change P hIncoming α.unop).op.obj V)).trans
          ((a.site α.unop V.unop).symm.trans
            ((congrArg (fun f => f ≫ G.map α) (NeighborhoodPairing.ι_desc P hIncoming F G a T.unop V)).symm.trans
              (Category.assoc _ _ _)))))

theorem toHom_fromHom (η : NeighborhoodInverseImage.presheaf P hIncoming F ⟶ G) :
    toHom P hIncoming F G (fromHom P hIncoming F G η) = η := by
  apply NatTrans.ext
  funext T
  apply colimit.hom_ext
  intro V
  exact colimit.ι_desc (cocone P hIncoming F G (fromHom P hIncoming F G η) T.unop) V

theorem fromHom_toHom (a : Pairing P hIncoming F G) :
    fromHom P hIncoming F G (toHom P hIncoming F G a) = a := by
  apply Pairing.ext
  funext T V
  exact colimit.ι_desc (cocone P hIncoming F G a T) (op V)

def equiv : (NeighborhoodInverseImage.presheaf P hIncoming F ⟶ G) ≃ Pairing P hIncoming F G where
  toFun := fromHom P hIncoming F G
  invFun := toHom P hIncoming F G
  left_inv := toHom_fromHom P hIncoming F G
  right_inv := fromHom_toHom P hIncoming F G

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodPairing
