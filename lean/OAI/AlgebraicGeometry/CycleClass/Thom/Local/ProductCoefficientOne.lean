import OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductTo
import OAI.AlgebraicGeometry.DivisorClass.Chern.LocalProductCoefficientOne

/-! # Product Coefficient One -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductCoefficientOne.Constructions

noncomputable section

/-! The genuine local cup-product coefficient equals one in every pair of
complex dimensions, including dimension zero. -/

open OAI.AlgebraicGeometry.DivisorClass.Chern.LocalProductCoefficientOne
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductTo.Constructions.Cocycle OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductHomologyCoefficient.Constructions

theorem localProductCupCoefficient_zero (c : ℕ) : HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient 0 c = 1 := by
  have h := ProductTo.Constructions.Cocycle.localProductCupCoefficient_cocycle 1 0 c
  simp only [Nat.add_zero, Nat.zero_add, DivisorClass.Chern.LocalProductCoefficientOne.localProductCupCoefficient_line, mul_one] at h
  exact h.symm

theorem localProductCupCoefficient_one (d c : ℕ) : HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient d c = 1 := by
  induction d with
  | zero => exact localProductCupCoefficient_zero c
  | succ d ih =>
      have h := ProductTo.Constructions.Cocycle.localProductCupCoefficient_cocycle 1 d c
      rw [DivisorClass.Chern.LocalProductCoefficientOne.localProductCupCoefficient_line, DivisorClass.Chern.LocalProductCoefficientOne.localProductCupCoefficient_line, one_mul, mul_one] at h
      simpa only [Nat.one_add] using h.trans ih

theorem localProductCupTop_eq_coordinate (d c : ℕ)
    (e : ((Fin d → ℂ) × (Fin c → ℂ)) ≃L[ℂ] (Fin (d + c) → ℂ)) :
    HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupTop d c = Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass e := by
  rw [HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupTop_eq_smul_coordinates d c e, localProductCupCoefficient_one, one_smul]

theorem localProductCrossCoefficient_one (d c : ℕ) : ProductHomologyCoefficient.Constructions.localProductCrossCoefficient d c = 1 := by
  rw [ProductHomologyCoefficient.Constructions.localProductCrossCoefficient_eq_inv, localProductCupCoefficient_one, inv_one]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductCoefficientOne.Constructions
