import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialProducts

/-! # Differential Product Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialProductBound.Construction

noncomputable section

/-! A differential product bound used to lower fixed-control order on curves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem relativeDifferential_mul_le_sup (k : Type*) {R : Type*}
    [CommRing k] [CommRing R] [Algebra k R] (I J : Ideal R) (n : ℕ) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (I * J) (n + 1) ≤
      I ⊔ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n := by
  let T := I ⊔ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  have hmul : I * J ≤ J * T ^ 1 := by
    rw [pow_one, mul_comm J]
    exact Ideal.mul_mono le_sup_left le_rfl
  exact (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k (n + 1) hmul).trans
    (Relative.DifferentialProducts.Construction.relativeDifferential_product_power_bound k J T n 1 le_sup_right)

/-- After one derivative has struck the first factor, at most `n`
derivatives can strike the second factor; the other terms stay in the first ideal. -/
theorem smoothDifferentialIdealSheaf_mul_le_sup {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J : X.IdealSheafData) (n : ℕ) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (I * J) (n + 1) ≤
      I ⊔ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n := by
  intro U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  exact relativeDifferential_mul_le_sup ℂ (I.ideal U) (J.ideal U) n

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialProductBound.Construction
