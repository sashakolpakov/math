import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange

/-! # Group Point Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange

noncomputable section

/-! Actual group-valued points commute with the original scheme
pullback, using its canonical adjunction and unchanged field points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductCoordinates

universe u

variable {S : Scheme.{u}} {T U A : Over S} [GrpObj A]

def groupTestIso (e : T ≅ U) : (T ⟶ A) ≃* (U ⟶ A) where
  toFun a := e.inv ≫ a
  invFun a := e.hom ≫ a
  left_inv a := by simp
  right_inv a := by simp
  map_mul' a b := MonObj.comp_mul e.inv a b

def pointPullbackGroupEquiv {S' : Scheme.{u}} (f : S' ⟶ S) (G : Grp (Over S)) :
    (Over.mk f ⟶ G.X) ≃*
      (Over.mk (𝟙 S') ⟶ ((Over.pullback f).mapGrp.obj G).X) := by
  let e : (Over.map f).obj (Over.mk (𝟙 S')) ≅ Over.mk f :=
    Over.isoMk (Iso.refl _) (by simp)
  exact (groupTestIso e.symm).trans (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G (Over.mk (𝟙 S')))

def baseChangedPointEquiv {S₁ S₂ S₀ : Scheme.{u}} (f : S₀ ⟶ S₁) (g : S₀ ⟶ S₂)
    (G : Grp (Over S₁)) (H : Grp (Over S₂))
    (e : (Over.pullback f).mapGrp.obj G ≅ (Over.pullback g).mapGrp.obj H) :
    (Over.mk f ⟶ G.X) ≃* (Over.mk g ⟶ H.X) :=
  (pointPullbackGroupEquiv f G).trans
    ((GroupProductCoordinates.groupSchemePointIso e).trans (pointPullbackGroupEquiv g H).symm)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
