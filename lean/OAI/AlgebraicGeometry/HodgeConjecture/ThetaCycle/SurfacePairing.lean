import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TopPairing
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SmoothConvergence

/-! # Surface Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfacePairing.CM

noncomputable section

/-!
ThetaCycle: the concrete conjugate pairing on compact complex surfaces.
Its continuity follows from the chart integrals, and its strict self-positivity
from the actual PolarizedPairing pure-form calculation.
-/

open scoped _root_.Manifold ContDiff _root_.Topology

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (Fin 2 → ℂ) X]
  [IsManifold 𝓘(ℝ, Fin 2 → ℂ) ∞ X] [T2Space X] [CompactSpace X]

/-- The ordinary complex-oriented chart integral of `α ∧ conjugate β`,
using the standard complex coordinate basis on a surface. -/
def surfaceConjugatePairing
    (α β : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin 2 → ℂ) X 2) : ℂ :=
  Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.topPairingWith (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.canonicalChartPartition (Fin 2 → ℂ) X) (Pi.basisFun ℂ (Fin 2))
    α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β)

theorem surface_conjugate_pairing_continuous
    (α : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin 2 → ℂ) X 2) :
    let _ := SmoothTopology.CM.smoothFormTopology (Fin 2 → ℂ) X 2
    Continuous (surfaceConjugatePairing α) :=
  TopPairing.CM.conjugate_top_pairing_continuous
    (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.canonicalChartPartition (Fin 2 → ℂ) X) (Pi.basisFun ℂ (Fin 2)) α

/-- A nonzero pure `(2,0)` form has strictly positive actual self-integral. -/
theorem surface_conjugate_pairing_positive
    (α : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin 2 → ℂ) X 2)
    (htype : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Fin 2 → ℂ) X 2 0 α.val) (hne : α ≠ 0) :
    (surfaceConjugatePairing α α).im = 0 ∧
      0 < (surfaceConjugatePairing α α).re ∧ surfaceConjugatePairing α α ≠ 0 := by
  have h := Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.topPairingWith_positive (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.canonicalChartPartition (Fin 2 → ℂ) X)
    (Pi.basisFun ℂ (Fin 2)) α htype hne
  norm_num only [show 2 * 2 = 4 from rfl, Complex.I_pow_four, one_mul] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfacePairing.CM
