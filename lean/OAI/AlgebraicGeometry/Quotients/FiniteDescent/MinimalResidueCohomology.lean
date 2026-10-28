import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex

/-! # Minimal Residue Cohomology -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent

noncomputable section

/-! The middle module of a minimal local complex computes the cohomology of its residue-field fiber. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (P : LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex S)

def LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex.baseChangeHomologyIso
    (K : Type u) [CommRing K] [Algebra R K] :
    (ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R K S).homology ≅
      (ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R K P.complex).homology :=
  ShortComplexEndpointHomotopy.Construction.LocalSectionLifting.shortComplexHomotopyEquivMapHomologyIso (ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R K) P.equivalence

def LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex.residueHomologyIso :
    (ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).homology ≅
      ModuleCat.of (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R ⊗[R] P.complex.X₂) :=
  P.baseChangeHomologyIso (IsLocalRing.ResidueField R) ≪≫
    (ShortComplex.LeftHomologyData.ofZeros
      (ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) P.complex)
      (ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex_f_zero R (IsLocalRing.ResidueField R) P.complex P.incoming_residue_zero)
      (ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex_g_zero R (IsLocalRing.ResidueField R) P.complex P.outgoing_residue_zero)).homologyIso

theorem LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex.middle_finrank_eq_residue_cohomology :
    Module.finrank R P.complex.X₂ = Module.finrank (IsLocalRing.ResidueField R)
      (ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).homology := by
  have h := P.residueHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank (IsLocalRing.ResidueField R)
      (ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).homology =
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] P.complex.X₂) at h
  rw [Module.finrank_baseChange] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent
