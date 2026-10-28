import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeGenerators
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrincipalLatticeDivision

/-! # Principal Basis -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PrincipalBasis.TestTransport

noncomputable section

/-! The literal original PEL principal subgroup, on the completed
images of the same integral lattice basis. -/

open scoped Classical

open _root_.Module

variable (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  {J : Type*} [Fintype J] [DecidableEq J]
  [Submodule.IsLattice ℚ P.lattice] (b : Basis J ℤ P.lattice)

omit [DecidableEq J] [Submodule.IsLattice ℚ P.lattice] in
theorem pelPrincipalLevel_iff_basis (N : ℕ) (hN : 0 < N) (g : P.FiniteSpecialUnitary) :
    g ∈ P.adelicPrincipalLevel N ↔
      (∀ j, g.val (LatticeGenerators.TestTransport.completedVectorBasis E P.lattice b j) ∈ P.completedLattice) ∧
      (∀ j, g.val.symm (LatticeGenerators.TestTransport.completedVectorBasis E P.lattice b j) ∈ P.completedLattice) ∧
      ∀ j, (N : ℚ)⁻¹ •
        (g.val (LatticeGenerators.TestTransport.completedVectorBasis E P.lattice b j) - LatticeGenerators.TestTransport.completedVectorBasis E P.lattice b j) ∈
          P.completedLattice :=
  PrincipalLatticeDivision.TestTransport.principalLattice_generators_division (LatticeCoordinates.TestTransport.completedVectorLattice E P.lattice)
    (LatticeGenerators.TestTransport.completedVectorBasis E P.lattice b) (LatticeGenerators.TestTransport.completedVectorLattice_span_basis E P.lattice b)
    N hN (g.val.restrictScalars AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PrincipalBasis.TestTransport
