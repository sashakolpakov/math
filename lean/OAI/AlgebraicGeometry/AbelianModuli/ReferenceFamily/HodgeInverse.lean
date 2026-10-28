import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne
import Mathlib.LinearAlgebra.Projection

/-! # Hodge Inverse -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse

noncomputable section

/-! The inverse of a rational Hodge isomorphism preserves Hodge type.
Both complementary summands are preserved by the forward map, so
injectivity rules out an antiholomorphic component in the inverse. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM

variable {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]

theorem isHodgeMap_inverse (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (K : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (e : U ≃ₗ[ℚ] V) (he : ComplexMultiplication.WeightOne.CM.IsHodgeMap H K e.toLinearMap) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap K H e.symm.toLinearMap := by
  intro x hx
  let eC := LinearEquiv.baseChange ℚ ℂ U V e
  obtain ⟨p, q, hpq, _⟩ := Submodule.existsUnique_add_of_isCompl H.complementary (eC.symm x)
  have hp : eC p ∈ K.holomorphic := he p p.property
  have hq : eC q ∈ K.antiholomorphic := he.map_antiholomorphic q.property
  have hsum : eC p + eC q = x :=
    (eC.map_add p q).symm.trans ((congrArg eC hpq).trans (eC.apply_symm_apply x))
  have hqeq : eC q = x - eC p := by
    rw [← hsum]
    abel
  have hqh : eC q ∈ K.holomorphic := hqeq.symm ▸ K.holomorphic.sub_mem hx hp
  have hqzero : (q : ComplexMultiplication.WeightOne.CM.Complexification U) = 0 :=
    eC.injective ((Submodule.disjoint_def.mp K.complementary.disjoint (eC q) hqh hq).trans eC.map_zero.symm)
  change eC.symm x ∈ H.holomorphic
  rw [← hpq, hqzero, add_zero]
  exact p.property

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse
