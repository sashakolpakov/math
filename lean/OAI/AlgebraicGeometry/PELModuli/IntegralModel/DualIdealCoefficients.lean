import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualNumberReduction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LiftDerivations

/-! # Dual Ideal Coefficients -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualIdealCoefficients

noncomputable section

/-! The actual square-zero ideal of dual numbers is its coefficient
module. This comparison preserves derivations and their coefficient scalars. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicLie

variable (k : Type) [Field k]

def dualIdealEquiv : DualNumberReduction.AlgebraicLie.dualIdeal k ≃ₗ[k] k where
  toFun v := v.val.snd
  invFun c := ⟨TrivSqZeroExt.inr c, by change (TrivSqZeroExt.inr c : DualNumber k).fst = 0; rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · exact v.property.symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
  [Algebra R k] [Algebra B k] [IsScalarTower R B k]

def derivationDualIdealEquiv : Derivation R B (DualNumberReduction.AlgebraicLie.dualIdeal k) ≃ₗ[k] Derivation R B k where
  toEquiv := ((dualIdealEquiv k).restrictScalars B).compDer.toEquiv
  map_add' := ((dualIdealEquiv k).restrictScalars B).compDer.map_add
  map_smul' c d := by
    apply Derivation.ext
    intro b
    exact (dualIdealEquiv k).map_smul c (d b)

theorem derivationDualIdealEquiv_apply (d : Derivation R B (DualNumberReduction.AlgebraicLie.dualIdeal k)) (b : B) :
    derivationDualIdealEquiv k R B d b = (d b).val.snd := rfl

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualIdealCoefficients
