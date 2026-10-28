import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Weil

/-! # Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Projection.CM

noncomputable section

/-! Construct GeometricTheta's bounded cotangent projection from the source's
symplectic coordinates and half-determinant, and prove its holomorphy. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixOperator : Matrix ι ι ℂ →L[ℂ] ((ι → ℂ) →L[ℂ] (ι → ℂ)) :=
  (Matrix.toLin'.trans LinearMap.toContinuousLinearMap).toLinearMap.toContinuousLinearMap

def coefficients : ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] (ι → ℂ) :=
  (ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := ℂ) ι).toContinuousLinearMap

theorem coefficients_apply (f : (ι → ℂ) →L[ℂ] ℂ) (i : ι) :
    coefficients f i = f (Pi.single i 1) := rfl

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}

def ambientCotangent : GeometricSource.CM.Ambient E →L[ℂ] (GeometricSource.CM.BallChart →L[ℂ] ℂ) :=
  (ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := ℂ) (Fin 2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 2 =>
      (show (Fin 3 → ℂ) →L[ℂ] ℂ from ContinuousLinearMap.proj i.castSucc).comp
        (show GeometricSource.CM.Ambient E →L[ℂ] (Fin 3 → ℂ) from ContinuousLinearMap.proj (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))

theorem ambientCotangent_apply (w : GeometricSource.CM.Ambient E) (ξ : GeometricSource.CM.BallChart) :
    ambientCotangent E w ξ = GeometricSource.CM.localPairing E B.b 1 ![ξ 0, ξ 1, 0] (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) := by
  change (∑ i : Fin 2, ξ i • w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) i.castSucc) = _
  simp [GeometricSource.CM.localPairing, Fin.sum_univ_succ, smul_eq_mul]

def graphOperator (L : GeometricSource.CM.LinePeriod E B places d) (z : GeometricSource.CM.BallChart) :
    (GeometricSource.CM.Positions E places → ℂ) →L[ℂ] GeometricSource.CM.Ambient E :=
  L.coordinates.complex.symm.toLinearMap.toContinuousLinearMap.comp
    ((matrixOperator (L.period z).matrix).prod (ContinuousLinearMap.id ℂ _))

theorem graphOperator_apply (L : GeometricSource.CM.LinePeriod E B places d) (z : GeometricSource.CM.BallChart)
    (x : GeometricSource.CM.Positions E places → ℂ) :
    graphOperator E L z x = GeometricSource.CM.graphInAmbient E L.coordinates (L.period z) x := rfl

def projection (L : GeometricSource.CM.LinePeriod E B places d) (z : GeometricSource.CM.BallChart) :
    ((GeometricSource.CM.Positions E places → ℂ) →L[ℂ] ℂ) →L[ℂ] (GeometricSource.CM.BallChart →L[ℂ] ℂ) :=
  (L.halfDet z : ℂ) •
    ((ambientCotangent E).comp ((graphOperator E L z).comp coefficients))

theorem projection_apply (L : GeometricSource.CM.LinePeriod E B places d) (z ξ : GeometricSource.CM.BallChart)
    (f : (GeometricSource.CM.Positions E places → ℂ) →L[ℂ] ℂ) :
    projection E L z f ξ = (L.halfDet z : ℂ) *
      GeometricSource.CM.localPairing E B.b 1 ![ξ 0, ξ 1, 0]
        (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z)
          (fun i => f (Pi.single i 1)) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) := by
  change (L.halfDet z : ℂ) * ambientCotangent E (graphOperator E L z (coefficients f)) ξ = _
  rw [ambientCotangent_apply, graphOperator_apply]
  rfl

theorem graphOperator_holomorphic (L : GeometricSource.CM.LinePeriod E B places d) :
    DifferentiableOn ℂ (graphOperator E L) B.domain := by
  let prodMap :
      (((GeometricSource.CM.Positions E places → ℂ) →L[ℂ] (GeometricSource.CM.Positions E places → ℂ)) ×
        ((GeometricSource.CM.Positions E places → ℂ) →L[ℂ] (GeometricSource.CM.Positions E places → ℂ))) →L[ℂ]
      ((GeometricSource.CM.Positions E places → ℂ) →L[ℂ]
        ((GeometricSource.CM.Positions E places → ℂ) × (GeometricSource.CM.Positions E places → ℂ))) :=
    (ContinuousLinearMap.prodₗᵢ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have hmat : DifferentiableOn ℂ (fun z => matrixOperator (L.period z).matrix) B.domain :=
    matrixOperator.differentiable.comp_differentiableOn L.holomorphic
  have hprod : DifferentiableOn ℂ (fun z =>
      (matrixOperator (L.period z).matrix).prod (ContinuousLinearMap.id ℂ _)) B.domain :=
    prodMap.differentiable.comp_differentiableOn
      (hmat.prodMk (differentiableOn_const _))
  exact (differentiableOn_const _).clm_comp hprod

/-- This is GeometricTheta's required holomorphic projection, derived from the
source period matrix and its specified half-determinant. -/
theorem projection_holomorphic (L : GeometricSource.CM.LinePeriod E B places d) :
    DifferentiableOn ℂ (projection E L) B.domain := by
  have hc := (graphOperator_holomorphic E L).clm_comp
    (differentiableOn_const (coefficients (ι := GeometricSource.CM.Positions E places)))
  have hp := (differentiableOn_const (ambientCotangent E)).clm_comp hc
  exact L.halfDet_holomorphic.smul hp

/-- The canonical GeometricTheta one-form equals the source's literal theta form. -/
theorem canonical_oneForm_eq_source (L : GeometricSource.CM.LinePeriod E B places d)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places)) (z ξ : GeometricSource.CM.BallChart) :
    RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (projection E L)
      (Weil.CM.finiteWeilInput φ) z ξ = GeometricSource.CM.thetaOneForm E L φ z ξ := by
  change projection E L z
    (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (Weil.CM.finiteWeilInput φ) (L.period z)) ξ = _
  rw [projection_apply, Weil.CM.source_one_form_eq_canonical_coefficient]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Projection.CM
