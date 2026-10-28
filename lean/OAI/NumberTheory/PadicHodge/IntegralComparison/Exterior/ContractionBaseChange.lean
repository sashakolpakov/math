import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorPowerBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulComplex

/-! # Contraction Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.ContractionBaseChange

noncomputable section

/-! Flat scalar extension commutes with the actual contraction differential
of the exterior Koszul complex, with its canonical exterior comparison. -/

open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction

universe u
variable (R S V : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] (s : Module.Dual R V)

def coefficient : Module.Dual S (S ⊗[R] V) :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp (s.baseChange S)

theorem coefficient_tmul (a : S) (v : V) :
    coefficient R S V s (a ⊗ₜ[R] v) = a * algebraMap R S (s v) := by
  change (TensorProduct.AlgebraTensorModule.rid R S S) (a ⊗ₜ[R] s v) = _
  simp [Algebra.smul_def, mul_comm]

abbrev ambientMap := GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.algebraMap R S V

theorem ambient_contraction (x : ExteriorAlgebra R V) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction S (S ⊗[R] V) (coefficient R S V s) (ambientMap R S V x) =
      ambientMap R S V (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V s x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [AlgHom.commutes]
      rw [IsScalarTower.algebraMap_apply R S (ExteriorAlgebra S (S ⊗[R] V))]
      simp [AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction, CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
      rw [map_mul, GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.algebraMap_ι,
        AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction_ι_mul, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction_ι_mul, map_sub, map_smul,
        map_mul, GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.algebraMap_ι, hx,
        coefficient_tmul, one_mul, algebraMap_smul]

variable [Module.Flat R S]

abbrev power (n : ℕ) := GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerEquiv R S V n

theorem power_coe_tmul (n : ℕ) (a : S) (x : ⋀[R]^n V) :
    ((power R S V n) (a ⊗ₜ[R] x) : ExteriorAlgebra S (S ⊗[R] V)) =
      a • ambientMap R S V x.val := by
  change GeometricComparison.Integral.ExteriorAlgebraBaseChange.IntegralExteriorBaseChange.algebraEquiv R S V (a ⊗ₜ[R] x.val) = _
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
  rfl

theorem contraction_tmul (n : ℕ) (a : S) (x : ⋀[R]^(n + 1) V) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction S (S ⊗[R] V) (coefficient R S V s) n
      (power R S V (n + 1) (a ⊗ₜ[R] x)) =
        power R S V n (a ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V s n x) := by
  apply Subtype.ext
  rw [AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction_coe, power_coe_tmul, map_smul, ambient_contraction, power_coe_tmul]
  rfl

theorem contraction_comp (n : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction S (S ⊗[R] V) (coefficient R S V s) n).comp
      (power R S V (n + 1)).toLinearMap =
        (power R S V n).toLinearMap.comp ((AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V s n).baseChange S) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => exact contraction_tmul R S V s n a x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.ContractionBaseChange
