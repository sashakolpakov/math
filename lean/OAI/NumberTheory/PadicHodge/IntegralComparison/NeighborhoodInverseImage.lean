import OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodRestriction

/-! # Neighborhood Inverse Image -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodInverseImage

noncomputable section

/-!
# IntegralComparison: the inverse-image presheaf from actual incoming neighborhoods
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Neighborhoods OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodColimit OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodRestriction

universe u v w u' v'

variable {C : Type u} [Category.{v} C] {A : Type w} [SemilatticeInf A]
  {D : Type u'} [Category.{v'} D] (P : A → ObjectProperty C)
  (hIncoming : ∀ V {T U : C}, (T ⟶ U) → P V U → P V T)
  [∀ T, HasColimitsOfShape (Incoming.Neighborhoods.Objects P T)ᵒᵖ D]

def presheaf (F : Aᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D where
  obj T := colimit (NeighborhoodColimit.diagram P T.unop F)
  map α := NeighborhoodRestriction.restriction P hIncoming α.unop F
  map_id T := NeighborhoodRestriction.restriction_id P hIncoming F T.unop
  map_comp α β := NeighborhoodRestriction.restriction_comp P hIncoming β.unop _ α.unop

def map {F G : Aᵒᵖ ⥤ D} (β : F ⟶ G) : presheaf P hIncoming F ⟶ presheaf P hIncoming G where
  app T := (NeighborhoodColimit.functor P T.unop).map β
  naturality _ U α := colimit.pre_map (Functor.whiskerLeft (Incoming.Neighborhoods.inclusion P U.unop).op β) (Incoming.Neighborhoods.change P hIncoming α.unop).op

def functor : (Aᵒᵖ ⥤ D) ⥤ (Cᵒᵖ ⥤ D) where
  obj := presheaf P hIncoming
  map := NeighborhoodInverseImage.map P hIncoming
  map_id F := by
    apply NatTrans.ext
    funext T
    exact (NeighborhoodColimit.functor P T.unop).map_id F
  map_comp β γ := by
    apply NatTrans.ext
    funext T
    exact (NeighborhoodColimit.functor P T.unop).map_comp β γ

instance preservesFiniteLimits [HasFiniteLimits D]
    [∀ T, HasExactColimitsOfShape (Incoming.Neighborhoods.Objects P T)ᵒᵖ D] :
    PreservesFiniteLimits (functor (D := D) P hIncoming) := by
  apply preservesFiniteLimits_of_evaluation
  intro T
  exact NeighborhoodColimit.preservesFiniteLimits P T.unop

instance preservesMonomorphisms [HasFiniteLimits D]
    [∀ T, HasExactColimitsOfShape (Incoming.Neighborhoods.Objects P T)ᵒᵖ D] :
    (functor (D := D) P hIncoming).PreservesMonomorphisms := by infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodInverseImage
