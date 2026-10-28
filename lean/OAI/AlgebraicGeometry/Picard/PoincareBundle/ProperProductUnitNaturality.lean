import OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperProductLineUnits

/-! # Proper Product Unit Naturality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperProductUnitNaturality

noncomputable section

/-! Parameter units are natural under arbitrary maps of proper products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperProductLineUnits

variable {k : Type u} [Field k] [IsAlgClosed k]
  {T U A : Over (Spec (.of k))} [IsProper A.hom] [IsIntegral A.left]

/-- The product map may also change the proper coordinate; only its parameter map matters. -/
theorem baseUnit_natural (a : U ⟶ T) (g : U ⊗ A ⟶ T ⊗ A)
    (hg : g ≫ fst T A = fst U A ≫ a) (r : Γ((T ⊗ A).left, ⊤)ˣ) :
    ProperProductLineUnits.baseUnit U A (Units.map g.left.appTop.hom.toMonoidHom r) =
      Units.map a.left.appTop.hom.toMonoidHom (ProperProductLineUnits.baseUnit T A r) := by
  have hc : Units.map g.left.appTop.hom.toMonoidHom
      (Units.map (fst T A).left.appTop.hom.toMonoidHom (ProperProductLineUnits.baseUnit T A r)) =
      Units.map (fst U A).left.appTop.hom.toMonoidHom
        (Units.map a.left.appTop.hom.toMonoidHom (ProperProductLineUnits.baseUnit T A r)) := by
    apply Units.ext
    change (g ≫ fst T A).left.appTop (ProperProductLineUnits.baseUnit T A r).val =
      (fst U A ≫ a).left.appTop (ProperProductLineUnits.baseUnit T A r).val
    rw [hg]
  apply ProperProductLineUnits.projection_units_injective U A
  exact (ProperProductLineUnits.pullback_baseUnit U A (Units.map g.left.appTop.hom.toMonoidHom r)).trans
    ((congrArg (Units.map g.left.appTop.hom.toMonoidHom) (ProperProductLineUnits.pullback_baseUnit T A r)).symm.trans hc)

/-- Restriction along any section recovers the same parameter unit. -/
theorem baseUnit_eq_section (s : T ⟶ T ⊗ A) (hs : s ≫ fst T A = 𝟙 T)
    (r : Γ((T ⊗ A).left, ⊤)ˣ) :
    ProperProductLineUnits.baseUnit T A r = Units.map s.left.appTop.hom.toMonoidHom r := by
  have hc := congrArg (Units.map s.left.appTop.hom.toMonoidHom) (ProperProductLineUnits.pullback_baseUnit T A r)
  apply Units.ext
  have hv := congrArg Units.val hc
  change (s ≫ fst T A).left.appTop (ProperProductLineUnits.baseUnit T A r).val =
    (Units.map s.left.appTop.hom.toMonoidHom r).val at hv
  rw [hs] at hv
  exact hv

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperProductUnitNaturality
