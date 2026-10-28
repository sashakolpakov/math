import OAI.RepresentationTheory.Theta.Geometric.MinimalEquationIdeal
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Minimal Field Extension Ranks -/

namespace OAI.RepresentationTheory.Theta.Geometric.MinimalFieldExtensionRanks

noncomputable section

/-! Minimal-complex ranks compute H0 and H1 after every local map to a
field, including the actual function ring of a geometric closed fiber. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

theorem baseChange_zero_of_residue_zero
    {R M N : Type u} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Free R N] (f : M →ₗ[R] N)
    (hf : f.baseChange (IsLocalRing.ResidueField R) = 0)
    (T : Type u) [Field T] [Algebra R T] [IsLocalHom (algebraMap R T)] :
    f.baseChange T = 0 := by
  let b := Module.Free.chooseBasis R N
  have hz (m : M) : (1 ⊗ₜ[R] f m : T ⊗[R] N) = 0 := by
    apply (Normalized.KernelBaseChange.tensor_one_eq_zero_iff_coefficients T b _).mpr
    have hk : (1 ⊗ₜ[R] f m : IsLocalRing.ResidueField R ⊗[R] N) = 0 := by
      change f.baseChange (IsLocalRing.ResidueField R) (1 ⊗ₜ[R] m) = 0
      rw [hf, LinearMap.zero_apply]
    have hc := (Normalized.KernelBaseChange.tensor_one_eq_zero_iff_coefficients (IsLocalRing.ResidueField R) b _).mp hk
    intro i
    exact (congrArg (IsLocalRing.ResidueField.lift (algebraMap R T)) (hc i)).trans (map_zero _)
  ext m
  exact hz m

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex S)
    (T : Type u) [Field T] [Algebra R T] [IsLocalHom (algebraMap R T)]

def minimalFieldFirstCyclesEquiv :
    LinearMap.ker (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R T S).f.hom ≃ₗ[T] (T ⊗[R] P.complex.X₁) :=
  (P.baseChangeFirstCyclesEquiv T).trans (LinearEquiv.ofTop _ (by
    change LinearMap.ker (P.complex.f.hom.baseChange T) = ⊤
    rw [baseChange_zero_of_residue_zero P.complex.f.hom P.incoming_residue_zero T,
      LinearMap.ker_zero]))

theorem minimal_first_finrank_eq_field_cycles :
    Module.finrank R P.complex.X₁ =
      Module.finrank T (LinearMap.ker (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R T S).f.hom) := by
  have h := (minimalFieldFirstCyclesEquiv P T).finrank_eq
  rw [Module.finrank_baseChange] at h
  exact h.symm

def minimalFieldHomologyIso :
    (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R T S).homology ≅ ModuleCat.of T (T ⊗[R] P.complex.X₂) :=
  P.baseChangeHomologyIso T ≪≫
    (ShortComplex.LeftHomologyData.ofZeros (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R T P.complex)
      (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex_f_zero R T P.complex
        (baseChange_zero_of_residue_zero P.complex.f.hom P.incoming_residue_zero T))
      (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex_g_zero R T P.complex
        (baseChange_zero_of_residue_zero P.complex.g.hom P.outgoing_residue_zero T))).homologyIso

theorem minimal_middle_finrank_eq_field_cohomology :
    Module.finrank R P.complex.X₂ = Module.finrank T (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R T S).homology := by
  have h := (minimalFieldHomologyIso P T).toLinearEquiv.finrank_eq
  change Module.finrank T (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R T S).homology =
    Module.finrank T (T ⊗[R] P.complex.X₂) at h
  rw [Module.finrank_baseChange] at h
  exact h.symm

end

end OAI.RepresentationTheory.Theta.Geometric.MinimalFieldExtensionRanks
