import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LinePeriods
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Weil
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF

/-! # Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Projection.CM

noncomputable section

section

/-! Holomorphic regularity of the literal HeckeCycles theta derivative and its
actual cotangent projection. The finite Schwartz input stays fixed. -/

open scoped Classical ContDiff _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Weil.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}

theorem source_first_holomorphic (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) :
    DifferentiableOn ℂ (fun z => fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ (L.period z)) 0) B.domain := by
  have he : (fun z => fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ (L.period z)) 0) =
      (fun z => RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient
        (RepresentationTheory.Theta.Geometric.LinearTheta.toDerivativeFactorizationInput (HeckeCycles.Theta.Weil.CM.finiteWeilInput φ)) (L.period z).matrix) := by
    funext z
    exact HeckeCycles.Theta.Weil.CM.source_first_is_canonical φ (L.period z)
  rw [he]
  intro z hz
  exact (RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice.firstCoefficient_differentiableAt
    (RepresentationTheory.Theta.Geometric.LinearTheta.toDerivativeFactorizationInput (HeckeCycles.Theta.Weil.CM.finiteWeilInput φ)) (L.period z)).comp_differentiableWithinAt
      z (L.holomorphic z hz)

def sourceGraphGradient (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (z : HeckeCycles.GeometricSource.CM.BallChart) : HeckeCycles.GeometricSource.CM.Ambient K :=
  HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z)
    (fun j => fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ (L.period z)) 0 (Pi.single j 1))

theorem source_graph_gradient_holomorphic (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) :
    DifferentiableOn ℂ (sourceGraphGradient K L φ) B.domain := by
  let c : HeckeCycles.GeometricSource.CM.BallChart → HeckeCycles.GeometricSource.CM.Positions K places → ℂ := fun z j =>
    fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ (L.period z)) 0 (Pi.single j 1)
  have hc : DifferentiableOn ℂ c B.domain := by
    apply differentiableOn_pi.mpr
    intro j
    exact (source_first_holomorphic K L φ).clm_apply (differentiableOn_const (Pi.single j 1))
  have hm := L.holomorphic
  have hu : DifferentiableOn ℂ (fun z => (L.period z).matrix.mulVec (c z)) B.domain := by
    apply differentiableOn_pi.mpr
    intro j
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  exact L.coordinates.complex.symm.toContinuousLinearEquiv.differentiable.comp_differentiableOn
    (hu.prodMk hc)

def sourceThetaCovector (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (z : HeckeCycles.GeometricSource.CM.BallChart) : HeckeCycles.GeometricSource.CM.BallChart →L[ℂ] ℂ :=
  ((L.halfDet z : ℂ) * sourceGraphGradient K L φ z (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) 0) •
      ContinuousLinearMap.proj (0 : Fin 2) +
    ((L.halfDet z : ℂ) * sourceGraphGradient K L φ z (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) 1) •
      ContinuousLinearMap.proj (1 : Fin 2)

theorem source_theta_covector_apply (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (z ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    sourceThetaCovector K L φ z ξ = HeckeCycles.GeometricSource.CM.thetaOneForm K L φ z ξ := by
  simp [sourceThetaCovector, HeckeCycles.GeometricSource.CM.thetaOneForm, sourceGraphGradient, HeckeCycles.GeometricSource.CM.localPairing,
    Fin.sum_univ_succ]
  ring

theorem source_theta_covector_holomorphic (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) :
    DifferentiableOn ℂ (sourceThetaCovector K L φ) B.domain := by
  have hw := source_graph_gradient_holomorphic K L φ
  have hh := L.halfDet_holomorphic
  unfold sourceThetaCovector
  fun_prop

theorem source_theta_covector_smooth (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) :
    ContDiffOn ℝ ∞ (sourceThetaCovector K L φ) B.domain := by
  exact (Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn
    B.domain_isOpen (source_theta_covector_holomorphic K L φ)).restrict_scalars ℝ

end

/-! The actual graph/half-determinant cotangent projection is surjective.
An explicit vector in the native prescribed frame realizes each covector. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}

def graphCotangent (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d) (z : HeckeCycles.GeometricSource.CM.BallChart)
    (c : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) : HeckeCycles.GeometricSource.CM.BallChart →L[ℂ] ℂ :=
  ((L.halfDet z : ℂ) * HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) c (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) 0) •
      ContinuousLinearMap.proj (0 : Fin 2) +
    ((L.halfDet z : ℂ) * HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) c (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) 1) •
      ContinuousLinearMap.proj (1 : Fin 2)

theorem graph_cotangent_surjective (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) : Function.Surjective (graphCotangent K L z) := by
  intro η
  let h : ℂ := L.halfDet z
  have hh : h ≠ 0 := Units.ne_zero _
  let v : HeckeCycles.GeometricSource.CM.Positions K places → ℂ := fun p =>
    ![0, η (Pi.single 0 1) / h, η (Pi.single 1 1) / h] p.2
  let w := Prescribed.CM.nativePeriodFrame K B places d z v
  have hw : HeckeCycles.GeometricSource.CM.prescribed K B places d z w :=
    (CoefficientPeriods.CM.native_frame_range K B places d z w).mp (LinearMap.mem_range_self _ v)
  let c := (L.coordinates.complex w).2
  have hgraph : HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) c = w := by
    apply L.coordinates.complex.injective
    change L.coordinates.complex (L.coordinates.complex.symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext ((L.graph_prescribed z hz w).mp hw).symm rfl
  have h0 : w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) 0 = η (Pi.single 0 1) / h := by
    have he := congrFun (Prescribed.CM.adapted_native_frame K B places d z v) (places.distinguished, 1)
    simpa [HeckeCycles.GeometricSource.CM.adaptedCoordinates, places.identity, v, w] using he
  have h1 : w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) 1 = η (Pi.single 1 1) / h := by
    have he := congrFun (Prescribed.CM.adapted_native_frame K B places d z v) (places.distinguished, 2)
    simpa [HeckeCycles.GeometricSource.CM.adaptedCoordinates, places.identity, v, w] using he
  refine ⟨c, ?_⟩
  apply ContinuousLinearMap.ext
  intro ξ
  have hξ : ξ = ξ 0 • (Pi.single 0 1 : HeckeCycles.GeometricSource.CM.BallChart) + ξ 1 • (Pi.single 1 1 : HeckeCycles.GeometricSource.CM.BallChart) := by
    funext j
    fin_cases j <;> simp
  change h * (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) c (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) 0) * ξ 0 +
    h * (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) c (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) 1) * ξ 1 = η ξ
  rw [hgraph, h0, h1, mul_div_cancel₀ _ hh, mul_div_cancel₀ _ hh]
  conv_rhs => rw [hξ, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

omit [IsGalois ℚ K] in
theorem source_covector_graph_projection (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    sourceThetaCovector K L φ z = graphCotangent K L z
      (fun j => fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ (L.period z)) 0 (Pi.single j 1)) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Projection.CM
