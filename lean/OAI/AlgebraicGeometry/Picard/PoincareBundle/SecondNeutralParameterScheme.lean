import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.ParameterScheme

/-! # Second Neutral Parameter Scheme -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralParameterScheme

noncomputable section

/-!
# The actual second neutral-axis parameter scheme and its normalized source unit
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {S : Scheme.{u}} (A X : Over S) [GrpObj X]

/-- The actual vertical neutral axis, with the first coordinate varying. -/
def point : A ⟶ A ⊗ X := lift (𝟙 A) (1 : A ⟶ X)

/-- Its second group coordinate is the identity. -/
theorem point_neutral : point A X ≫ snd A X = 1 := lift_snd _ _

/-- Pulling this parameter point back gives the corresponding second-neutral test point. -/
theorem point_comp {T : Over S} (z : T ⟶ A) : z ≫ point A X = lift z (1 : T ⟶ X) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [point, MonObj.comp_one]

variable (L : Line.Bundles.LineBundle (A ⊗ X).left) (D : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)

/-- The original vertical multiplication supplies its actual global neutral-axis frame. -/
def unitFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ Line.Fibers.fiber L (point A X) :=
  D.unitFrame (point A X) (point_neutral A X)

/-- This frame recovers the actual normalized unit at every second-neutral test point. -/
theorem unitFrame_natural {T : Over S} (z : T ⟶ A) :
    Line.Fibers.pullSection L z (point A X) (lift z (1 : T ⟶ X)) (point_comp A X z) (SecondNeutralParameterScheme.unitFrame A X L D).hom =
    (D.unitFrame (lift z (1 : T ⟶ X)) (lift_snd _ _)).hom :=
  D.unit_natural z (point A X) (lift z (1 : T ⟶ X)) (point_neutral A X) (lift_snd _ _) (point_comp A X z)

variable {A X} {B Y : Over S} [GrpObj Y] (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom g]

/-- The second neutral-axis square commutes with the actual quotient morphisms. -/
theorem point_naturality : f ≫ point B Y = point A X ≫ (f ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [point, MonObj.comp_one, MonObj.one_comp]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralParameterScheme
