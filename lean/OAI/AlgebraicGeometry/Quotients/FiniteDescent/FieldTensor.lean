import OAI.AlgebraicGeometry.Quotients.FiniteDescent.KernelSupportIs
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Field Tensor -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldTensor.Construction.FieldTensorSupport

noncomputable section

/-! A finite module is nonzero after tensoring with a field precisely at
the prime defined by that field-valued point. -/

open TensorProduct
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]
variable (K : Type u) [Field K] [Algebra R K]
variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem nontrivial_iff (p : PrimeSpectrum R) (hp : p.asIdeal = RingHom.ker (algebraMap R K)) :
    Nontrivial (K ⊗[R] M) ↔ p ∈ Module.support R M := by
  have hu : p.asIdeal.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap R K) := by
    intro r hr
    change IsUnit (algebraMap R K r)
    apply isUnit_iff_ne_zero.mpr
    intro he
    apply hr
    rw [hp]
    exact he
  let k := Ideal.ResidueField.lift p.asIdeal (algebraMap R K) hp.le hu
  let : Algebra p.asIdeal.ResidueField K := k.toAlgebra
  have : IsScalarTower R p.asIdeal.ResidueField K := by
    apply IsScalarTower.of_algebraMap_eq'
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p.asIdeal (algebraMap R K) hp.le hu r).symm
  let e := AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField K K M
  rw [← e.nontrivial_congr, Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right]
  exact (Module.mem_support_iff_nontrivial_residueField_tensorProduct (M := M) p).symm

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldTensor.Construction.FieldTensorSupport
