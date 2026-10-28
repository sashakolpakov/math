import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeCoordinates
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Lattice Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeTopology.TestTransport

noncomputable section

/-! The completion of the specified full integral lattice is compact
and open in the original PEL coefficient vector space. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

open _root_.Module

variable (E : Type) [Field E] [NumberField E]
  {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (L : Submodule ℤ (I → E)) [Submodule.IsLattice ℚ L] (b : Basis J ℤ L)

include b in
theorem completedVectorLattice_isOpen :
    IsOpen (LatticeCoordinates.TestTransport.completedVectorLattice E L : Set (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)) := by
  have he : (LatticeCoordinates.TestTransport.completedVectorLattice E L : Set (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)) =
      (CoefficientVectorCoordinates.TestTransport.coefficientVectorHomeomorph E (b.extendOfIsLattice ℚ).equivFun) ⁻¹'
        (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := J) : Set (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
    ext x
    exact LatticeCoordinates.TestTransport.completedVectorLattice_coordinates E L b x
  rw [he]
  exact RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isOpen.preimage (CoefficientVectorCoordinates.TestTransport.coefficientVectorHomeomorph E _).continuous

include b in
theorem completedVectorLattice_isCompact :
    IsCompact (LatticeCoordinates.TestTransport.completedVectorLattice E L : Set (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)) := by
  let e := CoefficientVectorCoordinates.TestTransport.coefficientVectorHomeomorph E (b.extendOfIsLattice ℚ).equivFun
  have he : (LatticeCoordinates.TestTransport.completedVectorLattice E L : Set (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)) =
      e.symm '' (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := J) : Set (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, (LatticeCoordinates.TestTransport.completedVectorLattice_coordinates E L b x).mp hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      apply (LatticeCoordinates.TestTransport.completedVectorLattice_coordinates E L b (e.symm y)).mpr
      change ∀ j, e (e.symm y) j ∈ AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles
      rw [e.apply_symm_apply]
      exact hy
  rw [he]
  exact RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isCompact.image e.symm.continuous

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeTopology.TestTransport
