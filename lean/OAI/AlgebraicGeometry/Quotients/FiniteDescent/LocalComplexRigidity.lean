import Mathlib.RingTheory.LocalRing.Module

/-! # Local Complex Rigidity -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalComplexRigidity.Construction.LocalSectionLifting

noncomputable section

/-! The local-ring linear algebra used to lift a fiberwise trivialization from a finite free complex. -/

open scoped TensorProduct

universe u v w w'

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]

theorem linearMap_injective_of_residue_injective (b : M →ₗ[R] N)
    (hb : Function.Injective (b.lTensor (IsLocalRing.ResidueField R))) : Function.Injective b := by
  obtain ⟨r, hr⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective b).mpr hb
  exact Function.HasLeftInverse.injective ⟨r, LinearMap.congr_fun hr⟩

theorem linearMap_eq_zero_of_residue_injective_comp
    {P : Type w'} [AddCommGroup P] [Module R P] (d : P →ₗ[R] M) (b : M →ₗ[R] N)
    (hb : Function.Injective (b.lTensor (IsLocalRing.ResidueField R))) (hd : b.comp d = 0) : d = 0 := by
  apply LinearMap.ext
  intro x
  apply linearMap_injective_of_residue_injective b hb
  exact (LinearMap.congr_fun hd x).trans (map_zero b).symm

theorem local_differential_eq_zero_of_detecting_map
    {P : Type w'} [AddCommGroup P] [Module R P]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (d : P →ₗ[R] M) (d' : Q →ₗ[R] N) (a : P →ₗ[R] Q) (b : M →ₗ[R] N)
    (hcomm : b.comp d = d'.comp a) (hd' : d' = 0)
    (hb : Function.Injective (b.lTensor (IsLocalRing.ResidueField R))) : d = 0 := by
  apply linearMap_eq_zero_of_residue_injective_comp d b hb
  rw [hcomm, hd', LinearMap.zero_comp]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalComplexRigidity.Construction.LocalSectionLifting
