import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceHalfDetAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallProjectiveCotangent
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Projection
import OAI.RepresentationTheory.Hecke.RadialDilation.SiegelFrame

/-! # Source First Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFirstCovariance.CM

noncomputable section

section

/-! ThetaCycle: normalize the actual rational oscillator input by the derived
geometric half-determinant, with one constant sign on the original ball. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K]
  [NumberField.IsCMField K] {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
  (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)
  (hdet : LinearMap.det g.toLinearMap = 1)

include hg hdet in
theorem source_geometric_multiplier_holomorphic :
    DifferentiableOn ℂ (SourceHalfDetAction.CM.sourceGeometricMultiplier K L g) B.domain := by
  have hd : DifferentiableOn ℂ
      (fun z => (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z) 2) B.domain :=
    (CMExtraction.ProjectiveCotangent.Frame.denominator_differentiable (BallFrameMatrices.CM.ballEmbeddingSL K g hdet 1)).differentiableOn
  have hn : DifferentiableOn ℂ (fun z => (L.halfDet (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z) : ℂ)) B.domain :=
    L.halfDet_holomorphic.comp (BallLineAction.CM.ball_line_action_holomorphic K B g hg)
      (fun z hz => BallLineAction.CM.ball_line_action_mem K B g hg ⟨z, hz⟩)
  simpa only [SourceHalfDetAction.CM.sourceGeometricMultiplier, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using!
    (hd.mul L.halfDet_holomorphic).mul (hn.inv (fun z _ => (L.halfDet (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z)).ne_zero))

omit [IsGalois ℚ K] in
include hg in
theorem source_geometric_multiplier_ne_zero (z : B.Domain) :
    SourceHalfDetAction.CM.sourceGeometricMultiplier K L g z.val ≠ 0 :=
  div_ne_zero (mul_ne_zero (BallLineAction.CM.ball_action_denominator_ne_zero K B g hg z) (L.halfDet z.val).ne_zero)
    (L.halfDet (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)).ne_zero

include hdet in
theorem source_geometric_multiplier_sign :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ ∀ z : B.Domain,
      SourceHalfDetAction.CM.sourceGeometricMultiplier K L g z.val =
        σ * IndexedCovariance.CM.indexedThetaMultiplier (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg) (L.period z.val) := by
  let : Nonempty (HeckeCycles.GeometricSource.CM.Positions K places) := ⟨(places.distinguished, 0)⟩
  have hs : IsPreconnected B.domain :=
    (isConnected_iff_connectedSpace.mpr (BallConnected.CM.ball_domain_connected B)).isPreconnected
  have hm := (IndexedCovariance.CM.indexed_theta_multiplier_holomorphic
    (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg) L.period L.holomorphic).continuousOn
  have he : Set.EqOn ((SourceHalfDetAction.CM.sourceGeometricMultiplier K L g) ^ 2)
      ((fun z => IndexedCovariance.CM.indexedThetaMultiplier (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg) (L.period z)) ^ 2)
      B.domain := by
    intro z hz
    exact (SourceHalfDetAction.CM.source_geometric_multiplier_square K L g hg hdet ⟨z, hz⟩).trans
      (IndexedCovariance.CM.indexed_theta_multiplier_square _ _).symm
  rcases hs.eq_or_eq_neg_of_sq_eq
    (source_geometric_multiplier_holomorphic K L g hg hdet).continuousOn hm he
    (fun {z} _ => IndexedCovariance.CM.indexed_theta_multiplier_ne_zero _ (L.period z)) with h | h
  · exact ⟨1, Or.inl rfl, fun z => (h z.property).trans (one_mul _).symm⟩
  · exact ⟨-1, Or.inr rfl, fun z => by simpa only [Pi.neg_apply, neg_one_mul] using h z.property⟩

include hdet in
theorem exists_source_geometric_finite_input (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) :
    ∃ Ψ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places), ∀ z : B.Domain, ∀ ξ : HeckeCycles.GeometricSource.CM.Positions K places → ℂ,
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ (L.period (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val))
          ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)).jacobiChange (L.period z.val) ξ) =
        SourceHalfDetAction.CM.sourceGeometricMultiplier K L g z.val * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (L.period z.val) ξ := by
  obtain ⟨σ, _, hσ⟩ := source_geometric_multiplier_sign K L g hg hdet
  refine ⟨RepresentationTheory.Theta.Kernel.Factorization.scaleInput σ (IndexedCovariance.CM.indexedFiniteOscillatorInput (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg) φ), ?_⟩
  intro z ξ
  rw [NormalizedCovariance.CM.completed_scale_finite_input, SourcePeriodAction.CM.source_ball_period_transform K L g hg z,
    IndexedCovariance.CM.indexed_completed_theta_covariance, hσ z, mul_assoc]

end

/-! ThetaCycle: geometric normalization of the actual completed theta series
gives covariance of its literal source first derivative and ambient graph
gradient, with no independently supplied coefficient identification. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Weil.CM OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization
open OAI.RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization

theorem source_completed_hasFDerivAt {I : Type*} [Fintype I]
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    HasFDerivAt (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) (fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ Z) 0) 0 := by
  rw [HeckeCycles.Theta.Weil.CM.source_first_is_canonical]
  simpa only using! (RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice.first_derivatives_uncorrected_holomorphic φ Z).2.1

theorem source_first_covariance_of_completed {I : Type*} [Fintype I] [DecidableEq I]
    (γ : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I ℝ) (Z Z' : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (φ Ψ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) (c : ℂ)
    (h : ∀ ξ, RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ Z' (γ.jacobiChange Z ξ) = c * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ) :
    (fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries Ψ Z') 0).comp (γ.jacobiChange Z) =
      c • fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries φ Z) 0 := by
  have hnew : HasFDerivAt (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ Z') (fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries Ψ Z') 0)
      ((γ.jacobiChange Z) 0) := by simpa only [map_zero] using source_completed_hasFDerivAt Ψ Z'
  have hn := hnew.comp 0 (γ.jacobiChange Z).hasFDerivAt
  have he : (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ Z') ∘ γ.jacobiChange Z = c • RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z := funext h
  rw [he] at hn
  exact hn.unique ((source_completed_hasFDerivAt φ Z).const_smul c)

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K]
  [NumberField.IsCMField K] {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
  (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)

theorem source_graph_gradient_covariance_of_completed
    (φ Ψ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z : B.Domain)
    (h : ∀ ξ : HeckeCycles.GeometricSource.CM.Positions K places → ℂ,
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ (L.period (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val))
          ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)).jacobiChange (L.period z.val) ξ) =
        SourceHalfDetAction.CM.sourceGeometricMultiplier K L g z.val * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (L.period z.val) ξ) :
    Projection.CM.sourceGraphGradient K L Ψ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) =
      SourceHalfDetAction.CM.sourceGeometricMultiplier K L g z.val • SourceSymplecticAction.CM.ballAmbientAction K g (Projection.CM.sourceGraphGradient K L φ z.val) := by
  have hc := source_first_covariance_of_completed
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg))
    (L.period z.val) (L.period (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)) φ Ψ
    (SourceHalfDetAction.CM.sourceGeometricMultiplier K L g z.val) h
  have hv := RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradient_of_covariance (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg))
    (L.period z.val) _ _ _ hc
  change HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val))
    (RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector (fderiv ℂ (HeckeCycles.GeometricSource.CM.thetaSeries Ψ (L.period (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val))) 0)) = _
  rw [hv, map_smul, ← SourceHalfDetAction.CM.source_graph_action K L g hg z]
  rfl

include hg in
theorem exists_source_graph_gradient_covariant_input
    (hdet : LinearMap.det g.toLinearMap = 1) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) :
    ∃ Ψ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places), ∀ z : B.Domain,
      Projection.CM.sourceGraphGradient K L Ψ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) =
        SourceHalfDetAction.CM.sourceGeometricMultiplier K L g z.val • SourceSymplecticAction.CM.ballAmbientAction K g (Projection.CM.sourceGraphGradient K L φ z.val) := by
  obtain ⟨Ψ, hΨ⟩ := exists_source_geometric_finite_input K L g hg hdet φ
  exact ⟨Ψ, fun z => source_graph_gradient_covariance_of_completed K L g hg φ Ψ z (hΨ z)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFirstCovariance.CM
