import OAI.NumberTheory.PadicHodge.IntegralComparison.PairingSections

/-! # Neighborhood Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodAdjunction

noncomputable section

/-!
# IntegralComparison: neighborhood inverse image is left adjoint to incoming sections
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Neighborhoods OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodColimit

universe u v w

variable {C : Type u} [Category.{v} C] {A : Type w} [SemilatticeInf A]
  (R : Type u) [CommRing R] (P : A → ObjectProperty C) (hP : Monotone P)
  (hIncoming : ∀ V {T U : C}, (T ⟶ U) → P V U → P V T)
  [∀ T, HasColimitsOfShape (Incoming.Neighborhoods.Objects P T)ᵒᵖ (ModuleCat.{u} R)]

def homEquiv (F : Aᵒᵖ ⥤ ModuleCat.{u} R) (G : Cᵒᵖ ⥤ ModuleCat.{u} R) :
    (NeighborhoodInverseImage.presheaf P hIncoming F ⟶ G) ≃
      (F ⟶ Incoming.SectionPresheaf.presheaf R (ModuleCat.of R R) P hP G) :=
  (NeighborhoodPairing.equiv P hIncoming F G).trans (PairingSections.equiv R P hP hIncoming F G)

theorem naturality_left {F F' : Aᵒᵖ ⥤ ModuleCat.{u} R} (β : F' ⟶ F)
    {G : Cᵒᵖ ⥤ ModuleCat.{u} R} (a : NeighborhoodInverseImage.presheaf P hIncoming F ⟶ G) :
    NeighborhoodAdjunction.homEquiv R P hP hIncoming F' G ((NeighborhoodInverseImage.functor P hIncoming).map β ≫ a) =
      β ≫ NeighborhoodAdjunction.homEquiv R P hP hIncoming F G a := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  have h := colimit.ι_map (Functor.whiskerLeft (Incoming.Neighborhoods.inclusion P T.unop.obj).op β)
    (op (⟨V.unop, T.unop.property⟩ : Incoming.Neighborhoods.Objects P T.unop.obj))
  have hx := congrArg (fun f : F'.obj V ⟶ colimit (NeighborhoodColimit.diagram P T.unop.obj F) =>
    a.app (op T.unop.obj) (f (r • x))) h
  change a.app (op T.unop.obj)
    ((NeighborhoodInverseImage.map P hIncoming β).app (op T.unop.obj)
      (colimit.ι (NeighborhoodColimit.diagram P T.unop.obj F') (op ⟨V.unop, T.unop.property⟩) (r • x))) =
    a.app (op T.unop.obj)
      (colimit.ι (NeighborhoodColimit.diagram P T.unop.obj F) (op ⟨V.unop, T.unop.property⟩) (r • β.app V x))
  exact hx.trans (congrArg (fun y => a.app (op T.unop.obj)
    (colimit.ι (NeighborhoodColimit.diagram P T.unop.obj F) (op ⟨V.unop, T.unop.property⟩) y))
      ((β.app V).hom.map_smul r x))

theorem naturality_right {F : Aᵒᵖ ⥤ ModuleCat.{u} R} {G G' : Cᵒᵖ ⥤ ModuleCat.{u} R}
    (a : NeighborhoodInverseImage.presheaf P hIncoming F ⟶ G) (β : G ⟶ G') :
    NeighborhoodAdjunction.homEquiv R P hP hIncoming F G' (a ≫ β) =
      NeighborhoodAdjunction.homEquiv R P hP hIncoming F G a ≫
        (Incoming.SectionPresheaf.functor R (ModuleCat.of R R) P hP).map β := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply NatTrans.ext
  funext T
  rfl

def adjunction : NeighborhoodInverseImage.functor P hIncoming ⊣
    Incoming.SectionPresheaf.functor R (ModuleCat.of R R) P hP :=
  Adjunction.mkOfHomEquiv
    { homEquiv := NeighborhoodAdjunction.homEquiv R P hP hIncoming
      homEquiv_naturality_left_symm := by
        intro F' F G β a
        apply (NeighborhoodAdjunction.homEquiv R P hP hIncoming F' G).injective
        exact ((NeighborhoodAdjunction.homEquiv R P hP hIncoming F' G).apply_symm_apply (β ≫ a)).trans
          ((naturality_left R P hP hIncoming β ((NeighborhoodAdjunction.homEquiv R P hP hIncoming F G).symm a)).trans
            (congrArg (fun b => β ≫ b) ((NeighborhoodAdjunction.homEquiv R P hP hIncoming F G).apply_symm_apply a))).symm
      homEquiv_naturality_right := naturality_right R P hP hIncoming }

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodAdjunction
