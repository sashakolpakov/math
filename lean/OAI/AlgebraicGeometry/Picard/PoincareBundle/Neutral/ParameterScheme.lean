import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

/-! # Parameter Scheme -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.ParameterScheme

noncomputable section

/-!
# The actual neutral-axis parameter scheme and its normalized source unit
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {S : Scheme.{u}} (A X : Over S) [GrpObj A]

/-- The actual horizontal neutral axis, with its second coordinate varying. -/
def point : X ⟶ A ⊗ X := lift (1 : X ⟶ A) (𝟙 X)

/-- The group coordinate of this parameter point is the identity. -/
theorem point_neutral : point A X ≫ fst A X = 1 := lift_fst _ _

/-- Pulling back the neutral parameter point yields precisely the corresponding neutral test point. -/
theorem point_comp {T : Over S} (z : T ⟶ X) : z ≫ point A X = lift (1 : T ⟶ A) z := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [point, MonObj.comp_one]

variable (L : Line.Bundles.LineBundle (A ⊗ X).left) (D : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)

/-- The original multiplication supplies an actual global unit frame on the neutral-axis pullback. -/
def unitFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ≅ Line.Fibers.fiber L (point A X) :=
  D.unitFrame (point A X) (point_neutral A X)

/-- This global unit frame recovers the original normalized unit at every neutral test point. -/
theorem unitFrame_natural {T : Over S} (z : T ⟶ X) :
    Line.Fibers.pullSection L z (point A X) (lift (1 : T ⟶ A) z) (point_comp A X z) (ParameterScheme.unitFrame A X L D).hom =
    (D.unitFrame (lift (1 : T ⟶ A) z) (lift_fst _ _)).hom :=
  D.unit_natural z (point A X) (lift (1 : T ⟶ A) z) (point_neutral A X) (lift_fst _ _) (point_comp A X z)

variable {A X} {B Y : Over S} [GrpObj B] (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f]

/-- The neutral-axis square commutes with the actual quotient maps. -/
theorem point_naturality : g ≫ point B Y = point A X ≫ (f ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [point, MonObj.comp_one, MonObj.one_comp]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.ParameterScheme
