import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormOneScalar
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq

/-! # Scalar Determinant -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarDeterminant.CM.Period

/-! Norm-one scalar multiplication preserves every original prescribed
Lagrangian, hence fixes its actual Siegel period matrix. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PeriodCovariance
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormOneScalar.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (r : Eˣ)

theorem pairing_smul_right (τ : Gal(E/ℚ)) (c : ℂ) (x y : GeometricSource.CM.Vec ℂ) :
    GeometricSource.CM.localPairing E B.b τ x (c • y) = c * GeometricSource.CM.localPairing E B.b τ x y := by
  simp only [GeometricSource.CM.localPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem prescribed_forward (z : GeometricSource.CM.BallChart) (w : GeometricSource.CM.Ambient E)
    (hw : GeometricSource.CM.prescribed E B places d z w) : GeometricSource.CM.prescribed E B places d z (NormOneScalar.CM.ambient E r w) := by
  intro i
  have hi := hw i
  by_cases hid : i = places.distinguished
  · subst i
    rw [ite_eq_left rfl] at hi ⊢
    constructor
    · exact (ℂ ∙ GeometricSource.CM.BallDatum.lineVector z).smul_mem
        (((places.representative places.distinguished) (r : E) : E) : ℂ) hi.1
    · change GeometricSource.CM.localPairing E B.b (places.representative places.distinguished)
        (GeometricSource.CM.BallDatum.lineVector z)
        ((((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative places.distinguished) (r : E) : E) : ℂ) •
          w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative places.distinguished)) = 0
      rw [pairing_smul_right, hi.2, mul_zero]
  · rw [ite_eq_right hid] at hi ⊢
    split_ifs with hd
    · rw [ite_eq_left hd] at hi
      change (((places.representative i) (r : E) : E) : ℂ) • w (places.representative i) = 0
      rw [hi, smul_zero]
    · rw [ite_eq_right hd] at hi
      change (((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative i) (r : E) : E) : ℂ) •
        w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative i) = 0
      rw [hi, smul_zero]

variable (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)

theorem transformed_graph (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (x : GeometricSource.CM.Positions E places → ℂ) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).complexify.numerator (L.period z).matrix).mulVec x =
      (L.period z).matrix.mulVec
        (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).complexify.denominator (L.period z).matrix).mulVec x) := by
  let w := GeometricSource.CM.graphInAmbient E L.coordinates (L.period z) x
  let w' := NormOneScalar.CM.ambient E r w
  have hp : GeometricSource.CM.prescribed E B places d z w' :=
    prescribed_forward E r z w (UnitaryEq.CM.PeriodCovariance.graph_prescribed E L z hz x)
  have hgraph := (L.graph_prescribed z hz w').mp hp
  have he :
      Sum.elim
        (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).complexify.numerator (L.period z).matrix).mulVec x)
        (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).complexify.denominator (L.period z).matrix).mulVec x) =
      ComplexAction.CM.complexFrame E L.coordinates w' := by
    rw [← UnitaryEq.CM.PeriodCovariance.block_graph_action, ← UnitaryEq.CM.PeriodCovariance.complexFrame_graph E L z x]
    exact NormOneScalar.CM.complex_matrix_frame E L.coordinates r hr w
  have hu := congrArg (fun p : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℂ =>
    fun i => p (.inl i)) he
  have hl := congrArg (fun p : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℂ =>
    fun i => p (.inr i)) he
  exact hu.trans (hgraph.trans (congrArg (L.period z).matrix.mulVec hl.symm))

theorem period_fixed (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    L.period z = (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).transformSiegel (L.period z) := by
  let G := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)
  have hm : G.complexify.numerator (L.period z).matrix =
      (L.period z).matrix * G.complexify.denominator (L.period z).matrix := by
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec]
    exact transformed_graph E L r hr z hz x
  have he : (L.period z).matrix = (G.transformSiegel (L.period z)).matrix := by
    change _ = G.complexify.numerator (L.period z).matrix *
      (G.complexify.denominator (L.period z).matrix)⁻¹
    rw [hm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (G.denominator_det_isUnit (L.period z)),
      Matrix.mul_one]
  generalize L.period z = Z at he ⊢
  generalize G.transformSiegel Z = W at he ⊢
  cases Z
  cases W
  cases he
  rfl

theorem graph_action (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (x : GeometricSource.CM.Positions E places → ℂ) :
    GeometricSource.CM.graphInAmbient E L.coordinates (L.period z)
      (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).complexify.denominator (L.period z).matrix).mulVec x) =
      NormOneScalar.CM.ambient E r (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z) x) := by
  apply (ComplexAction.CM.complexFrame E L.coordinates).injective
  rw [UnitaryEq.CM.PeriodCovariance.complexFrame_graph, ← NormOneScalar.CM.complex_matrix_frame, UnitaryEq.CM.PeriodCovariance.complexFrame_graph,
    UnitaryEq.CM.PeriodCovariance.block_graph_action]
  have he := transformed_graph E L r hr z hz x
  change Sum.elim _ _ = Sum.elim _ _
  rw [he]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarDeterminant.CM.Period

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarDeterminant.CM

/-! The scalar's determinant is computed on the original adapted
Lagrangian frame. Its equality with the Siegel denominator determinant
uses the source half-determinant to prove that frame is invertible. -/

open scoped Classical BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormOneScalar.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarDeterminant.CM.Period

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  (places : GeometricSource.CM.Places E) (d : Gal(E/ℚ) → Bool) (r : Eˣ)

def weight (p : GeometricSource.CM.Positions E places) : ℂ :=
  if p.1 = places.distinguished then
    if p.2 = 0 then ((places.representative p.1 (r : E) : E) : ℂ)
    else (((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative p.1) (r : E) : E) : ℂ)
  else if d (places.representative p.1) then
    (((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative p.1) (r : E) : E) : ℂ)
  else ((places.representative p.1 (r : E) : E) : ℂ)

def coordinateAction : Module.End ℂ (GeometricSource.CM.Positions E places → ℂ) :=
  Matrix.toLin' (Matrix.diagonal (weight E places d r))

theorem adapted_action (w : GeometricSource.CM.Ambient E) :
    GeometricSource.CM.adaptedCoordinates E places d (NormOneScalar.CM.ambient E r w) =
      coordinateAction E places d r (GeometricSource.CM.adaptedCoordinates E places d w) := by
  ext p
  simp only [coordinateAction, Matrix.toLin'_apply, Matrix.mulVec_diagonal,
    GeometricSource.CM.adaptedCoordinates, LinearMap.coe_mk, AddHom.coe_mk, weight]
  split_ifs <;> rfl

theorem coordinateAction_det : LinearMap.det (coordinateAction E places d r) =
    ∏ p, weight E places d r p := by
  rw [coordinateAction, LinearMap.det_toLin', Matrix.det_diagonal]

variable {places d} {B : GeometricSource.CM.BallDatum E} (L : GeometricSource.CM.LinePeriod E B places d)
  (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)

def adaptedGraph (z : GeometricSource.CM.BallChart) : Module.End ℂ (GeometricSource.CM.Positions E places → ℂ) :=
  (GeometricSource.CM.adaptedCoordinates E places d).comp (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z))

theorem adaptedGraph_det_ne_zero (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    LinearMap.det (adaptedGraph E L z) ≠ 0 := by
  rw [adaptedGraph, ← L.halfDet_square z hz]
  exact pow_ne_zero 2 (Units.ne_zero (L.halfDet z))

theorem graph_coordinate_action (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (adaptedGraph E L z).comp (Matrix.toLin'
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).complexify.denominator (L.period z).matrix)) =
      (coordinateAction E places d r).comp (adaptedGraph E L z) := by
  apply LinearMap.ext
  intro x
  change GeometricSource.CM.adaptedCoordinates E places d (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z)
      (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).complexify.denominator (L.period z).matrix).mulVec x)) = _
  rw [Period.graph_action E L r hr z hz, adapted_action]
  rfl

theorem denominator_det (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).complexify.denominator (L.period z).matrix).det =
      ∏ p, weight E places d r p := by
  have h := congrArg LinearMap.det (graph_coordinate_action E r L hr z hz)
  rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_toLin', coordinateAction_det] at h
  apply mul_left_cancel₀ (adaptedGraph_det_ne_zero E L z hz)
  exact h.trans (mul_comm _ _)

theorem halfDet_square (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z) ^ 2 =
      ∏ p, weight E places d r p := by
  rw [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_sq]
  exact denominator_det E r L hr z hz

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarDeterminant.CM

end

end OAI
