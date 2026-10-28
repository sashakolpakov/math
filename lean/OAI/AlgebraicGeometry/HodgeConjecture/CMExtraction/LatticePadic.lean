import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicCoordinateSplit

/-! # Lattice Padic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticePadic.TestTransport

noncomputable section

/-! The original completed lattice in retained basis coordinates,
tested at every rational prime. -/

open scoped Classical

open _root_.Module

variable (E : Type) [Field E] [NumberField E]
  {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (L : Submodule ℤ (I → E)) [Submodule.IsLattice ℚ L] (b : Basis J ℤ L)

theorem completedVectorLattice_padic_coordinates (x : I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    x ∈ LatticeCoordinates.TestTransport.completedVectorLattice E L ↔ ∀ j, ∀ (p : ℕ) [Fact p.Prime],
      ‖RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun x j)‖ ≤ 1 := by
  rw [LatticeCoordinates.TestTransport.completedVectorLattice_coordinates E L b x]
  exact forall_congr' (fun j => AdelicCoordinateSplit.TestTransport.integralFiniteAdeles_padic_iff _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticePadic.TestTransport
