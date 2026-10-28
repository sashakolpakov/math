import OAI.NumberTheory.PadicHodge.GeometricComparison.FixedFrameEq

/-! # Functor Inverse Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.FunctorInverseCoordinates

noncomputable section

/-! Inverses of cochain maps of functors are computed by taking
the inverse at each degree and object. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A] [Preadditive A]
  {K L : CochainComplex (C ⥤ A) ℕ} (a : K ⟶ L) [IsIso a]

theorem inverse (q : ℕ) (c : C) :
    ((inv a).f q).app c = inv ((a.f q).app c) :=
  (HomologicalComplex.eval (C ⥤ A) (.up ℕ) q ⋙ (evaluation C A).obj c).map_inv a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.FunctorInverseCoordinates
