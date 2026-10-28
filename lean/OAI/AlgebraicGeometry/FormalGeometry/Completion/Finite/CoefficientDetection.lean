import OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtInverseLimit
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientTower

/-! # Coefficient Detection -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection.Construction

noncomputable section

/-!
# Completion: finite reductions detect actual integral H¹

The coefficient inverse limit and surjective degree-zero transitions apply
to the actual Ext¹ definition. In particular, integral H¹ is ℓ-adically separated.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})

/-- Vanishing at every finite coefficient level detects zero in actual integral H¹. -/
theorem integralEllAdicH1_eq_zero_of_finiteReduction
    (x : X.EllAdicCohomology ℓ 1)
    (hx : ∀ n, CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n X 1 x = 0) : x = 0 := by
  exact ExtInverseLimit.Construction.ext_one_eq_zero_of_inverseLimit (CoefficientTower.Construction.finiteCoefficientTower ℓ X)
    (CoefficientTower.Construction.integralCoefficientCone ℓ X) (CoefficientTower.Construction.integralCoefficientConeIsLimit ℓ X)
    (ProetalePullback.Construction.proEtIntegerConstant X)
    (fun n => CoefficientTower.Construction.finiteEllAdicTransition_constantHom_surjective ℓ X n (n + 1)
      (Nat.le_succ n)) x hx

/-- Two actual integral H¹ classes agree if all their finite reductions agree. -/
theorem integralEllAdicH1_ext_finiteReduction
    (x y : X.EllAdicCohomology ℓ 1)
    (h : ∀ n, CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n X 1 x =
      CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n X 1 y) : x = y := by
  apply sub_eq_zero.mp
  apply integralEllAdicH1_eq_zero_of_finiteReduction ℓ X
  intro n
  rw [map_sub, h n, sub_self]

/-- The intersection of all ℓ-power multiples in actual integral H¹ is zero. -/
theorem integralEllAdicH1_separated (x : X.EllAdicCohomology ℓ 1)
    (hx : ∀ n, ∃ y : X.EllAdicCohomology ℓ 1, (ℓ : ℤ_[ℓ]) ^ n • y = x) :
    x = 0 := by
  apply integralEllAdicH1_eq_zero_of_finiteReduction ℓ X
  intro n
  exact (CoefficientCohomology.Construction.integralEllAdicFiniteReduction_one_eq_zero_iff ℓ n X x).mpr (hx n)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection.Construction
