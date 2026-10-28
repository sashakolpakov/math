import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.ProductDefect

/-! # Defect Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectCoordinates

noncomputable section

/-! Evaluate subgroup-product defects using any explicitly identified translated points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationDefect

variable {S : Scheme.{u}} {H A : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj A]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

theorem value_eq_defect {T : Over S} (x y z : T ⟶ A) (a b c : T ⟶ H)
    (hx : (a ≫ i) * x = y) (hy : (b ≫ i) * y = z) (hz : (c ≫ i) * x = z)
    (hc : a * b = c) :
    ProductDefect.value i L t a b x = TranslationDefect.defect i L t x y z a b c hx hy hz := by
  subst c
  subst y
  subst z
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectCoordinates
