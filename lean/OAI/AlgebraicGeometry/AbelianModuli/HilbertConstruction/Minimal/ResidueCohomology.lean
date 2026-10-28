import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MinimalShortComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BaseChangeComplex

/-! # Residue Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The middle module of a minimal local complex computes the cohomology of its residue-field fiber. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (P : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex S)

def Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.baseChangeHomologyIso
    (K : Type u) [CommRing K] [Algebra R K] :
    (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R K S).homology ≅
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R K P.complex).homology :=
  ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivMapHomologyIso (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R K) P.equivalence

def Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.residueHomologyIso :
    (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).homology ≅
      ModuleCat.of (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R ⊗[R] P.complex.X₂) :=
  P.baseChangeHomologyIso (IsLocalRing.ResidueField R) ≪≫
    (ShortComplex.LeftHomologyData.ofZeros
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) P.complex)
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex_f_zero R (IsLocalRing.ResidueField R) P.complex P.incoming_residue_zero)
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex_g_zero R (IsLocalRing.ResidueField R) P.complex P.outgoing_residue_zero)).homologyIso

theorem Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.middle_finrank_eq_residue_cohomology :
    Module.finrank R P.complex.X₂ = Module.finrank (IsLocalRing.ResidueField R)
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).homology := by
  have h := P.residueHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank (IsLocalRing.ResidueField R)
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).homology =
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] P.complex.X₂) at h
  rw [Module.finrank_baseChange] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
