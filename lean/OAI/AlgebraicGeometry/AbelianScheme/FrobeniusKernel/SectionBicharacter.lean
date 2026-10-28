import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBlocks
import Mathlib.Algebra.Group.Hom.Instances

/-! # Section Bicharacter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SectionBicharacter.Construction

noncomputable section

/-! A bilinear sheaf pairing supplies its actual bicharacter on every
section group. No pairing law is added as a hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {G H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G H) (T : Over S)

def sheafSectionBicharacter :
    G.obj.obj (.op T) →* H.obj.obj (.op T) →* (CartierDuality.CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb S).obj.obj (.op T) where
  toFun x := CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue H T (e.leftAdjoint.hom.app (.op T) x)
  map_one' := by
    apply MonoidHom.ext
    intro y
    exact (e.adjoint_value T 1 y).symm.trans
      (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T (e.rightAdjoint.hom.app (.op T) y)).map_one
  map_mul' x z := by
    apply MonoidHom.ext
    intro y
    exact (e.adjoint_value T (x * z) y).symm.trans
      (((CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T (e.rightAdjoint.hom.app (.op T) y)).map_mul x z).trans
        (congrArg₂ (· * ·) (e.adjoint_value T x y) (e.adjoint_value T z y)))

theorem sheafSectionBicharacter_right (x : G.obj.obj (.op T)) (y : H.obj.obj (.op T)) :
    sheafSectionBicharacter e T x y =
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T (e.rightAdjoint.hom.app (.op T) y) x :=
  (e.adjoint_value T x y).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SectionBicharacter.Construction
