import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeCoordinates

/-! # Integral Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.IntegralCoordinates.TestTransport

noncomputable section

/-! The original PEL completed lattice in its retained integral basis,
before passing from integral adeles to individual prime coordinates. -/

open scoped Classical

variable (E : Type) [Field E] [NumberField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  {J : Type*} [Fintype J] [DecidableEq J]
  [Submodule.IsLattice ℚ P.lattice] (b : Module.Basis J ℤ P.lattice)

theorem pel_completed_integral_coordinates (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    Y ∈ P.completedLattice ↔ ∀ j,
      CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun Y j ∈ AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles :=
  LatticeCoordinates.TestTransport.completedVectorLattice_coordinates E P.lattice b Y

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.IntegralCoordinates.TestTransport
