import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # First Biextension Factor -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

noncomputable section

/-!
# The first Poincare descent is an actual pullback through the quotient factorization

When a homomorphism `μ` factors as `f ≫ α`, its Poincare line on `A × X` is canonically the
pullback of the line defined by `α` on `B × X`. This step needs no kernel-frame choice.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {A B Z X : Over S}
  (P : Line.Bundles.LineBundle (Z ⊗ X).left)

/-- The genuine family line defined by a morphism into the first factor of the Poincare space. -/
def familyLine (μ : A ⟶ Z) : Line.Bundles.LineBundle (A ⊗ X).left :=
  P.pullback (μ ⊗ₘ 𝟙 X).left

variable (f : A ⟶ B) (μ : A ⟶ Z) (α : B ⟶ Z) (hα : f ≫ α = μ)

include hα in
/-- The factorization is an equality of actual relative product morphisms. -/
theorem product_factorization : (f ⊗ₘ 𝟙 X) ≫ (α ⊗ₘ 𝟙 X) = μ ⊗ₘ 𝟙 X := by
  rw [tensorHom_comp_tensorHom, hα, Category.id_comp]

/-- The first descended line is constructed directly on the quotient product. -/
def descendedLine : Line.Bundles.LineBundle (B ⊗ X).left := familyLine P α

/-- The canonical composition isomorphism recovers the original Poincare-family line. -/
def pullbackIso :
    (Scheme.Modules.pullback (f ⊗ₘ 𝟙 X).left).obj (descendedLine P α).sheaf ≅ (familyLine P μ).sheaf :=
  (Scheme.Modules.pullbackComp (f ⊗ₘ 𝟙 X).left (α ⊗ₘ 𝟙 X).left ≪≫
    Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (product_factorization f μ α hα))).app P.sheaf

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
