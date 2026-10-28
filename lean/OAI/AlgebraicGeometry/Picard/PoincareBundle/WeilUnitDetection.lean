import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafEvaluation

/-! # Weil Unit Detection -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilUnitDetection

noncomputable section

/-! Regular units detect the identity in the actual multiplicative fppf sheaf on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

universe u

/-- Evaluating the Laurent coordinate retains all information in the multiplicative-group section. -/
def unitValue {S : Scheme.{u}} (T : Over S) :
    (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb S).obj.obj (.op T) →* Γ(T.left, ⊤)ˣ :=
  (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T).comp MulEquiv.ulift.toMonoidHom

/-- The unit value is injective, including on nonreduced test schemes. -/
theorem injective {S : Scheme.{u}} (T : Over S) : Function.Injective (unitValue T) :=
  (AbelianScheme.CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective T).comp MulEquiv.ulift.injective

/-- Identity in the actual fppf multiplicative-group sheaf is detected by the regular unit. -/
theorem eq_one_iff {S : Scheme.{u}} (T : Over S) (x : (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb S).obj.obj (.op T)) :
    x = 1 ↔ unitValue T x = 1 := by
  constructor
  · rintro rfl
    exact (unitValue T).map_one
  · intro h
    exact WeilUnitDetection.injective T (h.trans (unitValue T).map_one.symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilUnitDetection
