import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Annihilator

/-! # Pairing Universal Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingUniversalValue.Construction

/-! A genuine scheme pairing is determined by its value on the
universal pair of points on the product scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem schemeBicharacter_eq_of_universal_value {S : Scheme.{u}} {A B W : Over S}
    [GrpObj A] [GrpObj B] [GrpObj W]
    (e d : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))
    (h : e.pairValue (fst A B) (snd A B) = d.pairValue (fst A B) (snd A B)) : e = d := by
  have hh : e.hom = d.hom := by
    simpa only [Annihilator.Construction.SchemeBicharacter.pairValue, lift_fst_snd, Category.id_comp] using h
  cases e
  cases d
  cases hh
  rfl

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingUniversalValue.Construction
