import Mathlib.CategoryTheory.Functor.Basic

/-! # Section Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SectionSquare

/-! A functorial comparison transports through a commuting section restriction square. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
  {A B G H U V : C} (a : A ⟶ G) (b : A ⟶ B) (d : B ⟶ H)
  (r : G ⟶ H) (u : G ⟶ U) (v : H ⟶ V) (k : U ⟶ V)

theorem square (h : F.map (a ≫ r) = F.map (b ≫ d)) (hs : u ≫ k = r ≫ v) :
    F.map ((a ≫ u) ≫ k) = F.map ((b ≫ d) ≫ v) := by
  calc
    _ = F.map (a ≫ (u ≫ k)) := congrArg F.map (Category.assoc _ _ _)
    _ = F.map (a ≫ (r ≫ v)) := congrArg (fun t => F.map (a ≫ t)) hs
    _ = F.map (a ≫ r) ≫ F.map v :=
      (congrArg F.map (Category.assoc _ _ _).symm).trans (F.map_comp _ _)
    _ = F.map (b ≫ d) ≫ F.map v := congrArg (fun t => t ≫ F.map v) h
    _ = F.map ((b ≫ d) ≫ v) := (F.map_comp _ _).symm

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SectionSquare
