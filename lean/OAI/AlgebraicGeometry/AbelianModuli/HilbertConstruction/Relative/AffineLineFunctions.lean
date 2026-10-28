import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Affine Line Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AffineLineFunctions

noncomputable section

/-! Relative regular functions are represented by the affine line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def relativeAffineLine (S : Scheme.{u}) : Over S :=
  Over.mk (AffineSpace (PUnit.{u + 1}) S ↘ S)

def relativeFunctionPresheaf (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ Type u :=
  (Over.forget S).op ⋙ Scheme.Γ ⋙ forget CommRingCat

def relativeAffineLineFunctionEquiv {S : Scheme.{u}} (T : Over S) :
    (T ⟶ relativeAffineLine S) ≃ Γ(T.left, ⊤) where
  toFun f := f.left.appTop (AffineSpace.coord S PUnit.unit)
  invFun r := Over.homMk (AffineSpace.homOfVector T.hom (fun _ : PUnit.{u + 1} => r))
    (AffineSpace.homOfVector_over _ _)
  left_inv f := by
    apply Over.OverMorphism.ext
    apply AffineSpace.hom_ext
    · exact (AffineSpace.homOfVector_over _ _).trans f.w.symm
    · intro i
      cases i
      exact AffineSpace.homOfVector_appTop_coord _ _ _
  right_inv r := AffineSpace.homOfVector_appTop_coord _ _ _

theorem relativeAffineLineFunctionEquiv_comp {S : Scheme.{u}} {U T : Over S}
    (f : U ⟶ T) (g : T ⟶ relativeAffineLine S) :
    relativeAffineLineFunctionEquiv U (f ≫ g) = f.left.appTop (relativeAffineLineFunctionEquiv T g) := rfl

def relativeFunctionPresheafIso (S : Scheme.{u}) :
    yoneda.obj (relativeAffineLine S) ≅ relativeFunctionPresheaf S :=
  NatIso.ofComponents (fun T => (relativeAffineLineFunctionEquiv T.unop).toIso) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro g
    exact relativeAffineLineFunctionEquiv_comp f.unop g)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AffineLineFunctions
