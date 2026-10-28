import OAI.AlgebraicGeometry.Picard.Homomorphisms.IntrinsicModuleDescent

/-! # Descent Over Tests -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.DescentOverTests

noncomputable section

/-! Testing native descent compatibility over the original base covers all scheme-valued lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.IntrinsicModuleDescent.Construction

variable {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
  (D E : Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f.left) (e : D.module ≅ E.module)

/-- Every native quotient test scheme has a canonical structure map to the original base. -/
theorem hom_compatible
    (h : ∀ (T : Over S) (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x.left).map e.hom ≫ E.hom q.left x.left y.left
        (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
      D.hom q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫
        (Scheme.Modules.pullback y.left).map e.hom)
    {T : Scheme.{u}} (q : T ⟶ B.left) (x y : T ⟶ A.left) (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) :
    (Scheme.Modules.pullback x).map e.hom ≫ E.hom q x y hx hy =
      D.hom q x y hx hy ≫ (Scheme.Modules.pullback y).map e.hom := by
  let U : Over S := Over.mk (q ≫ B.hom)
  let q' : U ⟶ B := Over.homMk q rfl
  let x' : U ⟶ A := Over.homMk x (by
    change x ≫ A.hom = q ≫ B.hom
    rw [← hx, Category.assoc, Over.w f])
  let y' : U ⟶ A := Over.homMk y (by
    change y ≫ A.hom = q ≫ B.hom
    rw [← hy, Category.assoc, Over.w f])
  have hx' : x' ≫ f = q' := Over.OverMorphism.ext hx
  have hy' : y' ≫ f = q' := Over.OverMorphism.ext hy
  exact h U q' x' y' hx' hy'

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.DescentOverTests
