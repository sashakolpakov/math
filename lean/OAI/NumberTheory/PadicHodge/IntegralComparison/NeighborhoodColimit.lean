import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Neighborhoods

/-! # Neighborhood Colimit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodColimit

noncomputable section

/-!
# IntegralComparison: the local inverse-image value is a filtered colimit over actual incoming neighborhoods
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Neighborhoods

universe u v w u' v'

variable {C : Type u} [Category.{v} C] {A : Type w} [SemilatticeInf A] [OrderTop A]
  {D : Type u'} [Category.{v'} D] (P : A → ObjectProperty C) (T : C)
  [HasColimitsOfShape (Incoming.Neighborhoods.Objects P T)ᵒᵖ D]

def diagram (F : Aᵒᵖ ⥤ D) : (Incoming.Neighborhoods.Objects P T)ᵒᵖ ⥤ D := (Incoming.Neighborhoods.inclusion P T).op ⋙ F

def functor : (Aᵒᵖ ⥤ D) ⥤ D :=
  (Functor.whiskeringLeft (Incoming.Neighborhoods.Objects P T)ᵒᵖ Aᵒᵖ D).obj (Incoming.Neighborhoods.inclusion P T).op ⋙ colim

instance preservesFiniteLimits [HasFiniteLimits D] [HasExactColimitsOfShape (Incoming.Neighborhoods.Objects P T)ᵒᵖ D] :
    PreservesFiniteLimits (functor (D := D) P T) := by
  dsimp only [functor]
  infer_instance

instance preservesMonomorphisms [HasFiniteLimits D] [HasExactColimitsOfShape (Incoming.Neighborhoods.Objects P T)ᵒᵖ D] :
    (functor (D := D) P T).PreservesMonomorphisms := by infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodColimit
