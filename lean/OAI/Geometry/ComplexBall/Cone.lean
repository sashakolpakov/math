import OAI.Geometry.ComplexBall.Free
import OAI.Geometry.ComplexBall.CoveringAtlas
import OAI.Geometry.ComplexBall.NormalizeSubmersion

/-! # Cone -/

namespace OAI.Geometry.ComplexBall.Cone.ArithmeticQuotient

noncomputable section

section

/-! The complex manifold structure and holomorphic submersion on the actual
quotient of negative vectors by matrices and nonzero complex scalars. -/

open scoped Classical _root_.Manifold
open _root_.Topology Filter OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

variable (b : ℂ) (hb : b.re < 0) (Γ : Subgroup (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b))
  [ProperlyDiscontinuousSMul Γ (ArithmeticQuotientBoostBall.Ball b)] [IsCancelSMul Γ (ArithmeticQuotientBoostBall.Ball b)]

def coneBallProjection (w : ArithmeticQuotientBoostBall.Ball b) : Quotient (Free.ArithmeticQuotient.coneOrbitSetoid b Γ) :=
  Quotient.mk _ (ArithmeticQuotientBoostBall.liftBall b w)

lemma coneBallProjection_covering : IsQuotientCoveringMap (coneBallProjection b Γ) Γ := by
  have hf : IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel Γ (ArithmeticQuotientBoostBall.Ball b))) Γ :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  exact hf.homeomorph_comp (Free.ArithmeticQuotient.coneQuotientHomeomorph b Γ).symm

omit [ProperlyDiscontinuousSMul Γ (ArithmeticQuotientBoostBall.Ball b)] [IsCancelSMul Γ (ArithmeticQuotientBoostBall.Ball b)] in
lemma coneBallProjection_normalize (z : ArithmeticQuotientBoostBall.Cone b) :
    coneBallProjection b Γ (ArithmeticQuotientBoostBall.normalize b z) = Quotient.mk (Free.ArithmeticQuotient.coneOrbitSetoid b Γ) z := by
  apply Quotient.sound
  change (MulAction.orbitRel Γ (ArithmeticQuotientBoostBall.Ball b)) (ArithmeticQuotientBoostBall.normalize b (ArithmeticQuotientBoostBall.liftBall b (ArithmeticQuotientBoostBall.normalize b z))) (ArithmeticQuotientBoostBall.normalize b z)
  rw [ArithmeticQuotientBoostBall.normalize_lift]

@[instance_reducible] def coneQuotientAtlas : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates (Quotient (Free.ArithmeticQuotient.coneOrbitSetoid b Γ)) :=
  CoveringAtlas.ArithmeticQuotient.coveringBallAtlas b hb Γ (coneBallProjection b Γ) (coneBallProjection_covering b Γ)

lemma coneQuotientAtlas_isManifold :
    @IsManifold ℂ _ ArithmeticQuotientBoostBall.BallCoordinates _ _ ArithmeticQuotientBoostBall.BallCoordinates _ 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) 1
      (Quotient (Free.ArithmeticQuotient.coneOrbitSetoid b Γ)) _ (coneQuotientAtlas b hb Γ) :=
  CoveringAtlas.ArithmeticQuotient.coveringBallAtlas_isManifold b hb Γ (coneBallProjection b Γ) (coneBallProjection_covering b Γ)

lemma negativeCone_isOpen :
    IsOpen {x : ArithmeticQuotientEquationsData.Vec ℂ | (ArithmeticQuotientEquationsData.complexHermitian b (RingHom.id ℂ) x x).re < 0} := by
  apply isOpen_lt _ continuous_const
  unfold ArithmeticQuotientEquationsData.complexHermitian
  fun_prop

omit [ProperlyDiscontinuousSMul Γ (ArithmeticQuotientBoostBall.Ball b)] [IsCancelSMul Γ (ArithmeticQuotientBoostBall.Ball b)] in
lemma projection_eventuallyEq_normalized (z : ArithmeticQuotientBoostBall.Cone b) :
    ArithmeticQuotientEquationsData.projection b (RingHom.id ℂ) (Free.ArithmeticQuotient.coneOrbitSetoid b Γ) z =ᶠ[𝓝 z.val]
      (fun x => coneBallProjection b Γ ((QuotientAtlas.Arithmetic.ballInclusion b hb).symm (NormalizeSubmersion.ArithmeticQuotient.affineNormalize x))) := by
  filter_upwards [(negativeCone_isOpen b).mem_nhds z.property] with x hx
  rw [ArithmeticQuotientEquationsData.projection, dite_eq_left hx]
  have hn : (QuotientAtlas.Arithmetic.ballInclusion b hb).symm (NormalizeSubmersion.ArithmeticQuotient.affineNormalize x) = ArithmeticQuotientBoostBall.normalize b ⟨x, hx⟩ :=
    QuotientAtlas.Arithmetic.ballInclusion_symm_coe b hb (ArithmeticQuotientBoostBall.normalize b ⟨x, hx⟩)
  rw [hn]
  exact (coneBallProjection_normalize b Γ ⟨x, hx⟩).symm

lemma coneQuotient_projection_submersion (z : ArithmeticQuotientBoostBall.Cone b) :
    letI : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates (Quotient (Free.ArithmeticQuotient.coneOrbitSetoid b Γ)) := coneQuotientAtlas b hb Γ
    MDifferentiableAt 𝓘(ℂ, ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)
      (ArithmeticQuotientEquationsData.projection b (RingHom.id ℂ) (Free.ArithmeticQuotient.coneOrbitSetoid b Γ) z) z.val ∧
    Function.Surjective (mfderiv 𝓘(ℂ, ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)
      (ArithmeticQuotientEquationsData.projection b (RingHom.id ℂ) (Free.ArithmeticQuotient.coneOrbitSetoid b Γ) z) z.val) := by
  let : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates (Quotient (Free.ArithmeticQuotient.coneOrbitSetoid b Γ)) := coneQuotientAtlas b hb Γ
  let : IsManifold 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) 1 (Quotient (Free.ArithmeticQuotient.coneOrbitSetoid b Γ)) := coneQuotientAtlas_isManifold b hb Γ
  have hq := CoveringAtlas.ArithmeticQuotient.coveringBallProjection_submersion b hb Γ (coneBallProjection b Γ)
    (coneBallProjection_covering b Γ) (ArithmeticQuotientBoostBall.normalize b z)
  have hn := (NormalizeSubmersion.ArithmeticQuotient.differentiableAt_affineNormalize z.val (ArithmeticQuotientBoostBall.cone_last_ne_zero b z)).mdifferentiableAt
  have hd : MDifferentiableAt 𝓘(ℂ, ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)
      (fun x => coneBallProjection b Γ ((QuotientAtlas.Arithmetic.ballInclusion b hb).symm (NormalizeSubmersion.ArithmeticQuotient.affineNormalize x))) z.val :=
    MDifferentiableAt.comp (f := NormalizeSubmersion.ArithmeticQuotient.affineNormalize)
      (g := fun w => coneBallProjection b Γ ((QuotientAtlas.Arithmetic.ballInclusion b hb).symm w)) z.val hq.1 hn
  have hs : Function.Surjective (mfderiv 𝓘(ℂ, ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)
      (fun x => coneBallProjection b Γ ((QuotientAtlas.Arithmetic.ballInclusion b hb).symm (NormalizeSubmersion.ArithmeticQuotient.affineNormalize x))) z.val) := by
    have he := mfderiv_comp (f := NormalizeSubmersion.ArithmeticQuotient.affineNormalize)
      (g := fun w => coneBallProjection b Γ ((QuotientAtlas.Arithmetic.ballInclusion b hb).symm w)) z.val hq.1 hn
    refine he.symm ▸ ?_
    rw [mfderiv_eq_fderiv]
    exact hq.2.comp (NormalizeSubmersion.ArithmeticQuotient.affineNormalize_fderiv_surjective z.val (ArithmeticQuotientBoostBall.cone_last_ne_zero b z))
  have he := projection_eventuallyEq_normalized b hb Γ z
  refine ⟨he.mdifferentiableAt_iff.mpr hd, ?_⟩
  rw [he.mfderiv_eq]
  exact hs

end

/-! Compactness, separation, countability and connectedness of the actual
negative-vector quotient. -/

open scoped Classical
open _root_.Topology

lemma coneQuotient_topological_properties (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0)
    (Γ : Subgroup (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b)) [DiscreteTopology Γ]
    [CompactSpace (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b ⧸ Γ)] :
    CompactSpace (Quotient (Free.ArithmeticQuotient.coneOrbitSetoid b Γ)) ∧
      T2Space (Quotient (Free.ArithmeticQuotient.coneOrbitSetoid b Γ)) ∧
      SecondCountableTopology (Quotient (Free.ArithmeticQuotient.coneOrbitSetoid b Γ)) ∧
      ConnectedSpace (Quotient (Free.ArithmeticQuotient.coneOrbitSetoid b Γ)) := by
  let : ProperSMul (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (ArithmeticQuotientBoostBall.Ball b) := ArithmeticQuotientBoostBall.ballAction_proper b hbim hb
  let : ProperSMul Γ (ArithmeticQuotientBoostBall.Ball b) := inferInstance
  let : ConnectedSpace (ArithmeticQuotientBoostBall.Ball b) := ArithmeticQuotientBoostBall.ball_connected b hb
  let : CompactSpace (MulAction.orbitRel.Quotient Γ (ArithmeticQuotientBoostBall.Ball b)) := QuotientCompact.Arithmetic.ballQuotient_compact b hbim hb Γ
  let : SecondCountableTopology (MulAction.orbitRel.Quotient Γ (ArithmeticQuotientBoostBall.Ball b)) :=
    ContinuousConstSMul.secondCountableTopology
  let e := Free.ArithmeticQuotient.coneQuotientHomeomorph b Γ
  exact ⟨e.symm.compactSpace, e.isEmbedding.t2Space,
    e.isEmbedding.secondCountableTopology, e.symm.surjective.connectedSpace e.symm.continuous⟩

end

end OAI.Geometry.ComplexBall.Cone.ArithmeticQuotient
