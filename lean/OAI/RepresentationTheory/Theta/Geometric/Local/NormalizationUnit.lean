import OAI.RepresentationTheory.Theta.Geometric.MinimalNormalizedSections
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Normalization Unit -/

namespace OAI.RepresentationTheory.Theta.Geometric.Local.NormalizationUnit

noncomputable section

/-! A normalized section after a local scalar extension makes the
original rank-one normalization coefficient a unit in the local base. -/

open _root_.CategoryTheory
open scoped TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem rankOne_functional_isUnit_of_normalized (e : R ≃ₗ[R] M)
    (v : M →ₗ[R] R) (m : M) (hm : v m = 1) : IsUnit (v (e 1)) := by
  apply isUnit_iff_exists_inv'.mpr
  refine ⟨e.symm m, ?_⟩
  calc
    e.symm m * v (e 1) = v (e.symm m • e 1) := (map_smul v _ _).symm
    _ = v (e (e.symm m)) := congrArg v (Normalized.RankOneKernel.rankOne_apply e (e.symm m)).symm
    _ = 1 := (congrArg v (e.apply_symm_apply m)).trans hm

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex S)

theorem minimalSectionFunctional_isUnit_of_local_extension
    (T : Type u) [CommRing T] [Algebra R T] [IsLocalHom (algebraMap R T)]
    (e : R ≃ₗ[R] P.complex.X₁) (v : S.X₁ →ₗ[R] R)
    (hsection : ∃ m : T ⊗[R] S.X₁, S.f.hom.baseChange T m = 0 ∧
      Normalized.KernelBaseChange.scalarFunctionalBaseChange T v m = 1) :
    IsUnit (MinimalNormalizedSections.minimalSectionFunctional P v (e 1)) := by
  obtain ⟨m, _, hm⟩ := (MinimalNormalizedSections.normalized_minimal_cycles_iff P T v).mp hsection
  have hu := rankOne_functional_isUnit_of_normalized (Normalized.KernelBaseChange.rankOneBaseChange T e)
    (Normalized.KernelBaseChange.scalarFunctionalBaseChange T (MinimalNormalizedSections.minimalSectionFunctional P v)) m hm
  rw [Normalized.KernelBaseChange.rankOneBaseChange_one, Normalized.KernelBaseChange.scalarFunctionalBaseChange_tmul, mul_one] at hu
  exact hu.of_map (algebraMap R T)

end

end OAI.RepresentationTheory.Theta.Geometric.Local.NormalizationUnit
