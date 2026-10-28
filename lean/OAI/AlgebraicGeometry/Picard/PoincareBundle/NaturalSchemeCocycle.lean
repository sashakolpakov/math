import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalProductFrames

/-! # Natural Scheme Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalSchemeCocycle

/-! A natural regular two-cocycle on an actual group scheme, tested on all schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (H : Over S) [GrpObj H]

/-- These are the ordinary unit, symmetry, cocycle, and pullback laws of regular coefficients. -/
structure NaturalCocycle where
  value {T : Over S} (a b : T ⟶ H) : Γ(T.left, ⊤)ˣ
  natural {T U : Over S} (g : U ⟶ T) (a b : T ⟶ H) :
    Units.map g.left.appTop.hom (value a b) = value (g ≫ a) (g ≫ b)
  one_left {T : Over S} (a : T ⟶ H) : value 1 a = 1
  one_right {T : Over S} (a : T ⟶ H) : value a 1 = 1
  symmetric {T : Over S} (a b : T ⟶ H) : value a b = value b a
  cocycle {T : Over S} (a b c : T ⟶ H) :
    value (a * b) c * value a b = value a (b * c) * value b c

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalSchemeCocycle
