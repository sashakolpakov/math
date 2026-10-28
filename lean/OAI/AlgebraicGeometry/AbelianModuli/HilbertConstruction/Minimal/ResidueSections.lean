import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ResidueCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexFirstCycles

/-! # Residue Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The first module of a minimal nonnegative complex computes degree-zero cohomology on the fiber. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (P : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex S)

def Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.firstCyclesEquiv :
    LinearMap.ker S.f.hom ≃ₗ[R] LinearMap.ker P.complex.f.hom :=
  ShortComplexFirstCycles.LocalSectionLifting.shortComplexFirstCyclesEquiv P.equivalence P.hom_h₀ P.inv_h₀

def Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.baseChangeFirstCyclesEquiv
    (K : Type u) [CommRing K] [Algebra R K] :
    LinearMap.ker (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R K S).f.hom ≃ₗ[K]
      LinearMap.ker (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R K P.complex).f.hom :=
  ShortComplexFirstCycles.LocalSectionLifting.shortComplexFirstCyclesEquiv
    (ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivMap (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R K) P.equivalence)
    (ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivMap_hom_h₀ (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R K) P.equivalence P.hom_h₀)
    (ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivMap_inv_h₀ (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R K) P.equivalence P.inv_h₀)

def Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.residueFirstCyclesEquiv :
    LinearMap.ker (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).f.hom ≃ₗ[IsLocalRing.ResidueField R]
      (IsLocalRing.ResidueField R ⊗[R] P.complex.X₁) :=
  (P.baseChangeFirstCyclesEquiv (IsLocalRing.ResidueField R)).trans
    (LinearEquiv.ofTop _ (by
      change LinearMap.ker (P.complex.f.hom.baseChange (IsLocalRing.ResidueField R)) = ⊤
      rw [P.incoming_residue_zero, LinearMap.ker_zero]))

theorem Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.first_finrank_eq_residue_cycles :
    Module.finrank R P.complex.X₁ = Module.finrank (IsLocalRing.ResidueField R)
      (LinearMap.ker (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).f.hom) := by
  have h := P.residueFirstCyclesEquiv.finrank_eq
  rw [Module.finrank_baseChange] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
