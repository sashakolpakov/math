import Mathlib.CategoryTheory.Functor.Basic

/-! # Square Congr -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.SquareCongr.FunctorSquareCongr

/-! Transport a functorial square through four specified morphism equalities. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
  {P Q : C} {M N : D} (a a' : P ⟶ Q) (b b' : M ⟶ N)
  (c c' : F.obj P ⟶ M) (d d' : F.obj Q ⟶ N)

theorem square (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d')
    (h : F.map a' ≫ d' = c' ≫ b') : F.map a ≫ d = c ≫ b :=
  (congrArg₂ (fun x y => F.map x ≫ y) ha hd).trans
    (h.trans (congrArg₂ (fun x y => x ≫ y) hc hb).symm)

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.SquareCongr.FunctorSquareCongr
