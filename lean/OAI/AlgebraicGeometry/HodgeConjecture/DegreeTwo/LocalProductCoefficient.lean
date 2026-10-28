import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductCup
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality

/-! # Local Product Coefficient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions

noncomputable section

/-!
# DegreeTwo: the local product cup is a nonzero multiple of the ambient normal class

The coefficient is defined by the actual ambient local-cohomology
normalization. The cup–cross evaluation proves that it is nonzero.
The resulting equality holds for every complex-linear coordinate system.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles

set_option backward.isDefEq.respectTransparency false

def productFlattenCoordinates (d c : ℕ) :
    ((Fin d → ℂ) × (Fin c → ℂ)) ≃L[ℂ] (Fin (d+c) → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])

def productTopCohomologyIso (d c : ℕ) :
    CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology ((Fin d → ℂ) × (Fin c → ℂ)) (2*(d+c)) ≅ ModuleCat.of ℚ ℚ :=
  (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso (productFlattenCoordinates d c) (2*(d+c))).symm ≪≫
    CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso (d+c)

def localProductCupTop (d c : ℕ) :
    CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology ((Fin d → ℂ) × (Fin c → ℂ)) (2*(d+c)) :=
  eqToHom (congrArg (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology ((Fin d → ℂ) × (Fin c → ℂ)))
    (Nat.mul_add 2 d c).symm) (LocalProductCup.Constructions.localProductCupClass d c)

theorem localProductCupTop_ne_zero (d c : ℕ) : localProductCupTop d c ≠ 0 := by
  intro h
  have hi := (ModuleCat.mono_iff_injective
    (eqToHom (congrArg (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology ((Fin d → ℂ) × (Fin c → ℂ)))
      (Nat.mul_add 2 d c).symm))).mp inferInstance
  exact LocalProductCup.Constructions.localProductCupClass_ne_zero d c (hi (h.trans (map_zero _).symm))

def localProductCupCoefficient (d c : ℕ) : ℚ :=
  (productTopCohomologyIso d c).hom (localProductCupTop d c)

theorem localProductCupCoefficient_ne_zero (d c : ℕ) : localProductCupCoefficient d c ≠ 0 := by
  intro h
  apply localProductCupTop_ne_zero d c
  apply (ModuleCat.mono_iff_injective (productTopCohomologyIso d c).hom).mp inferInstance
  exact h.trans (map_zero _).symm

theorem productTopCohomologyIso_normalization (d c : ℕ) :
    (productTopCohomologyIso d c).hom (CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass (productFlattenCoordinates d c)) = 1 := by
  change (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso (d+c)).hom
    ((CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso (productFlattenCoordinates d c) (2*(d+c))).inv
      ((CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso (productFlattenCoordinates d c) (2*(d+c))).hom
        ((CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso (d+c)).inv 1))) = 1
  rw [Iso.hom_inv_id_apply,Iso.inv_hom_id_apply]

theorem localProductCupTop_eq_smul (d c : ℕ) :
    localProductCupTop d c = localProductCupCoefficient d c •
      CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass (productFlattenCoordinates d c) := by
  apply (ModuleCat.mono_iff_injective (productTopCohomologyIso d c).hom).mp inferInstance
  rw [map_smul,productTopCohomologyIso_normalization]
  exact (mul_one (localProductCupCoefficient d c)).symm

theorem localProductCupTop_eq_smul_coordinates (d c : ℕ)
    (e : ((Fin d → ℂ) × (Fin c → ℂ)) ≃L[ℂ] (Fin (d+c) → ℂ)) :
    localProductCupTop d c = localProductCupCoefficient d c • CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass e :=
  (localProductCupTop_eq_smul d c).trans
    (congrArg (fun a => localProductCupCoefficient d c • a)
      (CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass_eq (productFlattenCoordinates d c) e))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions
