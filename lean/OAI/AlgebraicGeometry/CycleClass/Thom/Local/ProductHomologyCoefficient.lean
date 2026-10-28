import OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductCoefficient

/-! # Product Homology Coefficient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductHomologyCoefficient

noncomputable section

/-! The local cross-product coefficient is the reciprocal of the actual
local cup coefficient, by canonical evaluation on the actual cross cycle. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates.Constructions

namespace Constructions

theorem relativeEvaluation_changeDegree (X : TopCat.{0}) (A : Set X) {n m : ℕ}
    (h : n = m) (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n)
    (z : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A n) :
    Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A m
      (eqToHom (congrArg (fun j => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A j) h) a)
      (eqToHom (congrArg (fun j => Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A j) h) z) =
        Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A n a z := by
  subst m
  rfl

def localProductCrossTop (d c : ℕ) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) ({0}ᶜ) (2 * (d + c)) :=
  eqToHom (congrArg (fun j => Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ
    (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) ({0}ᶜ) j) (Nat.mul_add 2 d c).symm)
      (HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions.localProductCrossGenerator d c)

theorem localProductCupTop_evaluation (d c : ℕ) :
    Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) ({0}ᶜ) (2 * (d + c))
      (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupTop d c) (localProductCrossTop d c) = 1 := by
  rw [HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupTop, localProductCrossTop,
    relativeEvaluation_changeDegree _ _ (Nat.mul_add 2 d c).symm]
  exact HodgeConjecture.DegreeTwo.LocalProductCup.Constructions.localProductCupClass_evaluation d c

def localProductCrossCoefficient (d c : ℕ) : ℚ :=
  HomologyCoordinates.Constructions.coordinateHomologyEquiv (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates d c) (localProductCrossTop d c)

theorem localProductCupCoefficient_mul_crossCoefficient (d c : ℕ) :
    HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient d c * localProductCrossCoefficient d c = 1 := by
  have h := localProductCupTop_evaluation d c
  rw [HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupTop_eq_smul] at h
  rw [localProductCrossCoefficient, HomologyCoordinates.Constructions.coordinateHomologyEquiv_eq_evaluation]
  simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using h

theorem localProductCrossCoefficient_eq_inv (d c : ℕ) :
    localProductCrossCoefficient d c = (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient d c)⁻¹ := by
  apply mul_left_cancel₀ (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient_ne_zero d c)
  rw [localProductCupCoefficient_mul_crossCoefficient,
    mul_inv_cancel₀ (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient_ne_zero d c)]

theorem localProductCrossCoefficient_ne_zero (d c : ℕ) :
    localProductCrossCoefficient d c ≠ 0 := by
  rw [localProductCrossCoefficient_eq_inv]
  exact inv_ne_zero (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient_ne_zero d c)

theorem localProductCrossTop_eq_smul_coordinates (d c : ℕ)
    (e : ((Fin d → ℂ) × (Fin c → ℂ)) ≃L[ℂ] (Fin (d + c) → ℂ)) :
    localProductCrossTop d c = localProductCrossCoefficient d c • HomologyCoordinates.Constructions.coordinateHomologyGenerator e := by
  apply (HomologyCoordinates.Constructions.coordinateHomologyEquiv e).injective
  rw [map_smul, HomologyCoordinates.Constructions.coordinateHomologyGenerator_normalization, smul_eq_mul, mul_one,
    ← HomologyCoordinates.Constructions.coordinateHomologyEquiv_eq (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates d c) e]
  rfl

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductHomologyCoefficient
