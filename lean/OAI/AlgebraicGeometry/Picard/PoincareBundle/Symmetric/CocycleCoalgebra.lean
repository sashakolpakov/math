import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleComultiplication

/-! # Cocycle Coalgebra -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.CocycleCoalgebra

noncomputable section

/-! A normalized symmetric two-cocycle gives a cocommutative coalgebra. -/

universe u v

open Coalgebra TensorProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.CoalgebraTensorMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleComultiplication

variable (k : Type u) (R : Type v) [CommRing k] [CommRing R] [Bialgebra k R]

/-- The ordinary cocycle, unit, and symmetry identities in the coordinate algebra. -/
structure IsNormalizedSymmetricCocycle (c : R ⊗[k] R) : Prop where
  cocycle : TensorProduct.assoc k R R R
      ((c ⊗ₜ[k] (1 : R)) * (comul (R := k) (A := R)).rTensor R c) =
    ((1 : R) ⊗ₜ[k] c) * (comul (R := k) (A := R)).lTensor R c
  counit_left : (counit (R := k) (A := R)).rTensor R c = 1
  counit_right : (counit (R := k) (A := R)).lTensor R c = 1
  symmetric : TensorProduct.comm k R R c = c

variable (c : R ⊗[k] R) (hc : IsNormalizedSymmetricCocycle k R c)

include hc

/-- The cocycle equation is exactly what makes the twisted comultiplication associative. -/
theorem coassoc_twisted :
    (TensorProduct.assoc k R R R).toLinearMap.comp
        (((CocycleComultiplication.twisted k R c).rTensor R).comp (CocycleComultiplication.twisted k R c)) =
      ((CocycleComultiplication.twisted k R c).lTensor R).comp (CocycleComultiplication.twisted k R c) := by
  apply LinearMap.ext
  intro a
  change TensorProduct.assoc k R R R ((CocycleComultiplication.twisted k R c).rTensor R (CocycleComultiplication.twisted k R c a)) =
    (CocycleComultiplication.twisted k R c).lTensor R (CocycleComultiplication.twisted k R c a)
  rw [CocycleComultiplication.rTensor_twisted, CocycleComultiplication.lTensor_twisted, CocycleComultiplication.twisted_apply,
    CoalgebraTensorMaps.comul_rTensor_mul, CoalgebraTensorMaps.comul_lTensor_mul, ← mul_assoc, CoalgebraTensorMaps.assoc_mul,
    hc.cocycle, coassoc_apply, mul_assoc]

/-- A genuine coalgebra structure, constructed from the cocycle identities. -/
@[instance_reducible]
def coalgebra : Coalgebra k R where
  comul := CocycleComultiplication.twisted k R c
  counit := counit
  coassoc := coassoc_twisted k R c hc
  rTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro a
    change (counit (R := k) (A := R)).rTensor R (c * comul a) = 1 ⊗ₜ[k] a
    rw [CoalgebraTensorMaps.counit_rTensor_mul, hc.counit_left, one_mul, rTensor_counit_comul]
  lTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro a
    change (counit (R := k) (A := R)).lTensor R (c * comul a) = a ⊗ₜ[k] 1
    rw [CoalgebraTensorMaps.counit_lTensor_mul, hc.counit_right, one_mul, lTensor_counit_comul]

variable [Coalgebra.IsCocomm k R]

/-- Symmetry of the cocycle preserves cocommutativity. -/
theorem cocomm : letI := coalgebra k R c hc; Coalgebra.IsCocomm k R := by
  refine @Coalgebra.IsCocomm.mk k R _ _ _ (coalgebra k R c hc) ?_
  apply LinearMap.ext
  intro a
  change TensorProduct.comm k R R (c * comul a) = c * comul a
  rw [CoalgebraTensorMaps.comm_mul, hc.symmetric, comm_comul]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.CocycleCoalgebra
