import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Differential

/-! # Functor Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.FunctorCoordinates

noncomputable section

/-! The native Čech functor acts on product coordinates by the actual coefficient presheaf map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R]

local instance moduleProducts : HasProducts.{v} (ModuleCat.{max u v} R) := by
  let h : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v, max u v}
  exact fun I => h.has_limits_of_shape (Discrete I)

variable {H J : Cᵒᵖ ⥤ ModuleCat.{max u v} R} (a : H ⟶ J)

theorem coordinate (n : ℕ) (t : Fin (n + 1) → ι) :
    ((NonemptyCechNerve.complexFunctor F).map a).f n ≫ Differential.coordinate F R J n t =
      Differential.coordinate F R H n t ≫ a.app (op (Presentation.TupleProducts.family F n t)) :=
  Limits.Pi.map_π (fun s => a.app (op (Presentation.TupleProducts.family F n s))) t

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.FunctorCoordinates
