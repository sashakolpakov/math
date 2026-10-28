import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource
import OAI.RepresentationTheory.Theta.Geometric.LinearTheta

/-! # Weil -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Weil.CM

noncomputable section

/-! The source's literal theta series is the canonical PoissonAutomorphy/DerivativeFactorization series
used by GeometricTheta. Its first derivative is therefore the same constructed
coefficient, rather than an independently supplied theta map. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable {ι : Type*} [Fintype ι]

def finiteWeilInput (φ : GeometricSource.CM.FiniteInput ι) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι :=
  ⟨φ.val, Submodule.subset_span φ.property⟩

theorem thetaSeries_eq_canonical (φ : GeometricSource.CM.FiniteInput ι) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    GeometricSource.CM.thetaSeries φ Z = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (finiteWeilInput φ) Z := by
  funext z
  apply tsum_congr
  intro x
  simp only [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm, finiteWeilInput,
    ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, Complex.ofReal_ratCast]
  have he : (∑ i, ∑ j, (x i : ℂ) * Z.matrix i j * (x j : ℂ)) =
      ∑ i, ∑ j, (x i : ℂ) * ((x j : ℂ) * Z.matrix i j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  rfl

theorem source_first_is_canonical (φ : GeometricSource.CM.FiniteInput ι) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    fderiv ℂ (GeometricSource.CM.thetaSeries φ Z) 0 =
      RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (finiteWeilInput φ) Z := by
  rw [thetaSeries_eq_canonical]
  exact (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst_hasFDerivAt (finiteWeilInput φ) Z).fderiv

/-- The source projection acts on exactly GeometricTheta's canonical first coefficient. -/
theorem source_one_form_eq_canonical_coefficient
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (z ξ : GeometricSource.CM.BallChart) :
    GeometricSource.CM.thetaOneForm E L φ z ξ =
      (L.halfDet z : ℂ) * GeometricSource.CM.localPairing E B.b 1 ![ξ 0, ξ 1, 0]
        (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z)
          (fun j => RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (finiteWeilInput φ) (L.period z)
            (Pi.single j 1)) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) := by
  unfold GeometricSource.CM.thetaOneForm
  rw [source_first_is_canonical]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Weil.CM
