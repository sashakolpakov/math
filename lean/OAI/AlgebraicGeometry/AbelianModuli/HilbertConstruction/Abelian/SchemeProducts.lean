import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Scheme Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! The relative product of two actual abelian schemes is an abelian scheme of the sum of their dimensions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g h : ℕ}

def Schemes.AbelianScheme.product (A : Schemes.AbelianScheme g S) (B : Schemes.AbelianScheme h S) : Schemes.AbelianScheme (g + h) S where
  scheme := A.scheme ⊗ B.scheme
  group := inferInstance
  commutative := inferInstance
  proper := inferInstanceAs (IsProper (pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom))
  smoothDimension := by
    have hp : SmoothOfRelativeDimension h (pullback.fst A.scheme.hom B.scheme.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange h).of_isPullback
        (IsPullback.of_hasPullback A.scheme.hom B.scheme.hom).flip B.smoothDimension
    have hc : SmoothOfRelativeDimension (h + g) (pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom) :=
      inferInstance
    exact (Nat.add_comm h g) ▸ hc
  connected := GeometricallyConnected.comp (pullback.fst A.scheme.hom B.scheme.hom) A.scheme.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
