import OAI.AlgebraicGeometry.AbelianVariety.PowerImage
import OAI.AlgebraicGeometry.AbelianVariety.CyclePeriods
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # De Rham -/

namespace OAI.AlgebraicGeometry.AbelianVariety.DeRham.Constructions.ExteriorCohomology

noncomputable section

open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

/-- Translation-invariant forms compute the actual de Rham cohomology of an abelian variety. -/
def abelianInvariantDeRhamEquiv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel) (G := A.variety.analyticSpace) n ≃ₗ[ℂ]
      A.variety.deRhamCohomology n := by
  let : ConnectedSpace A.variety.analyticSpace := PowerImage.Constructions.ExteriorCohomology.abelianPoint_connectedSpace A
  let : MeasurableSpace A.variety.analyticSpace := borel _
  let : BorelSpace A.variety.analyticSpace := ⟨rfl⟩
  exact CyclePeriods.Constructions.ExteriorCohomology.invariantDeRhamEquiv n

/-- Evaluation at the identity identifies actual cohomology with alternating covectors. -/
def abelianCovectorDeRhamEquiv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    (A.variety.analyticModel [⋀^Fin n]→L[ℝ] ℂ) ≃ₗ[ℂ]
      A.variety.deRhamCohomology n :=
  (InvariantClosed.Constructions.ExteriorCohomology.invariantFormsEvalEquiv (E := A.variety.analyticModel)
    (G := A.variety.analyticSpace) n).symm.trans (abelianInvariantDeRhamEquiv A n)

/-- The same isomorphism using the canonical integration-normalized Betti comparison. -/
def abelianCovectorBettiEquiv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    (A.variety.analyticModel [⋀^Fin n]→L[ℝ] ℂ) ≃ₗ[ℂ]
      A.variety.complexCohomology n :=
  (abelianCovectorDeRhamEquiv A n).trans (A.variety.deRhamBettiIso n).toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianVariety.DeRham.Constructions.ExteriorCohomology
