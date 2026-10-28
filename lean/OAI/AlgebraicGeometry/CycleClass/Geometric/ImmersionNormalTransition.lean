import OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalNormalSliceAction
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairTransition

/-! # Immersion Normal Transition -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalTransition

noncomputable section

/-!
# Normal-coordinate transition invariance of actual local rational classes

The genuine transition between two normal pairs preserves their full normal
zero locus. Its proved nonlinear rational-class action gives equality after
shrinking to coordinate balls. Pullback to the corresponding actual ambient
neighborhood then gives equality of the relative-cohomology germs.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Topology _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Analytic.ImmersionNormalPair

variable {M N E : Type} [TopologicalSpace N]
  [NormedAddCommGroup E]
  {f : M → N} {x : M} {p : ℕ}

private def normalNeighborhoodBallMap (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (r s : ℝ) (hr : P.radius ≤ r) (hs : P.radius ≤ s) :
    TopCat.of P.neighborhood ⟶
      TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s) :=
  (TopCat.isoOfHomeo P.homeomorph).hom ≫
    NormalNeighborhoodRestriction.Cycles.normalProductBallRadiusInclusion E (Fin p → ℂ) hr hs

private theorem normalNeighborhoodBallMap_mapsTo
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (r s : ℝ) (hr : P.radius ≤ r) (hs : P.radius ≤ s) (hspos : 0 < s) :
    Set.MapsTo (normalNeighborhoodBallMap P r s hr hs) P.relativeComplement
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hspos)) := by
  intro y hy hzero
  apply (P.mem_complement_iff y).mp hy
  exact congrArg Subtype.val hzero

private theorem normalNeighborhoodBallMap_projection
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (r s : ℝ) (hr : P.radius ≤ r) (hs : P.radius ≤ s) :
    normalNeighborhoodBallMap P r s hr hs ≫ NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E (Fin p → ℂ) r s =
      P.normalCoordinate := by
  ext y
  rfl

variable [NormedSpace ℝ E] [NormedSpace ℂ E]
variable (P Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)

/-- After an actual radius shrinking of the first normal pair, the second
normal-pair class restricts to precisely its normalized rational class. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.exists_rationalClassFin_restrict_eq_of_transition
    (he : (P.transition Q).MDifferentiable
      𝓘(ℂ, E × (Fin p → ℂ)) 𝓘(ℂ, E × (Fin p → ℂ))) :
    ∃ (t : ℝ) (ht : 0 < t) (htP : t ≤ P.radius),
      ∃ (hRQ : (P.restrictRadius t ht htP).neighborhood ⊆ Q.neighborhood),
        RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hRQ (Set.range f) (2 * p)
          Q.rationalClassFin = (P.restrictRadius t ht htP).rationalClassFin := by
  obtain ⟨r, s, hr, hs, hsub, hclass⟩ :=
    RationalNormalSliceAction.Cycles.exists_normalDiffeomorph_rationalClass_pullback (P.transition Q) he
      (P.zero_mem_transition_source Q) (P.transition_zero Q)
      (P.transition_preserves_zero Q)
  let t := min P.radius (min r s)
  have ht : 0 < t := lt_min P.radius_pos (lt_min hr hs)
  have htP : t ≤ P.radius := min_le_left _ _
  have htr : t ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hts : t ≤ s := (min_le_right _ _).trans (min_le_right _ _)
  let T := P.restrictRadius t ht htP
  have hTP : T.neighborhood ⊆ P.neighborhood := P.restrictRadius_neighborhood_subset t ht htP
  have hTQ : T.neighborhood ⊆ Q.neighborhood := by
    rintro y ⟨z, hz, rfl⟩
    have hz' := hsub ⟨Metric.ball_subset_ball htr hz.1, Metric.ball_subset_ball hts hz.2⟩
    rw [P.transition_source Q] at hz'
    exact hz'.2
  refine ⟨t, ht, htP, hTQ, ?_⟩
  let b := normalNeighborhoodBallMap T r s htr hts
  have hb := normalNeighborhoodBallMap_mapsTo T r s htr hts hs
  let ψ := NormalSliceLocalAction.Cycles.normalProductBallMap (P.transition Q) r s
    ((P.transition Q).continuousOn.mono hsub)
  have hψ := NormalSliceLocalAction.Cycles.normalProductBallMap_mapsTo (P.transition Q) r s hs
    ((P.transition Q).continuousOn.mono hsub) 0
    (fun z hz hne hzero => hne ((P.transition_preserves_zero Q z (hsub hz)).mp hzero))
  let i : TopCat.of T.neighborhood ⟶ TopCat.of Q.neighborhood :=
    LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of N)) hTQ
  have hi : Set.MapsTo i T.relativeComplement Q.relativeComplement := fun _ hy => hy
  have hmapQ : (b ≫ ψ) ≫ NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ) = i ≫ Q.normalCoordinate := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    change (Q.ambientChart (P.ambientChart.symm (P.ambientChart y.val))).2 =
      (Q.ambientChart y.val).2
    rw [P.ambientChart.left_inv (P.neighborhood_subset_source (hTP y.property))]
  have hcohQ :
      Q.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p) ≫
        RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hTQ (Set.range f) (2 * p) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ))
          (NormalProductPair.Cycles.normalProductProjection_mapsTo E (Fin p → ℂ) 0) (2 * p) ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) ψ hψ (2 * p) ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) b hb (2 * p) := by
    change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) Q.normalCoordinate
        Q.normalCoordinate_mapsTo (2 * p) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) i hi (2 * p) = _
    simp only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
    congr 1
    exact hmapQ.symm
  have hcohT :
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E (Fin p → ℂ) r s)
          (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection_mapsTo E (Fin p → ℂ) r s hs) (2 * p) ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) b hb (2 * p) =
      T.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p) := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
    unfold ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap
    congr 1
  have hclass' := congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) b hb (2 * p)) hclass
  rw [NormalProductPurity.Cycles.complexNormalProductRationalClass_eq_pullback] at hclass'
  change
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ))
        (NormalProductPair.Cycles.normalProductProjection_mapsTo E (Fin p → ℂ) 0) (2 * p) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) ψ hψ (2 * p) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) b hb (2 * p))
        (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E (Fin p → ℂ) r s)
        (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection_mapsTo E (Fin p → ℂ) r s hs) (2 * p) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) b hb (2 * p))
        (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) at hclass'
  rw [← hcohQ, hcohT] at hclass'
  rw [Q.rationalClassFin_eq_normalPullback, T.rationalClassFin_eq_normalPullback]
  exact hclass'

/-- Two genuine differentiable normal-coordinate systems at the same
point define the same actual relative-cohomology germ. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_germ_eq_of_transition
    (he : (P.transition Q).MDifferentiable
      𝓘(ℂ, E × (Fin p → ℂ)) 𝓘(ℂ, E × (Fin p → ℂ))) :
    P.relativeCohomologyGerm (2 * p) P.rationalClassFin =
      Q.relativeCohomologyGerm (2 * p) Q.rationalClassFin := by
  obtain ⟨t, ht, htP, hTQ, hclass⟩ := P.exists_rationalClassFin_restrict_eq_of_transition Q he
  let T := P.restrictRadius t ht htP
  have hTP : T.neighborhood ⊆ P.neighborhood := P.restrictRadius_neighborhood_subset t ht htP
  calc
    P.relativeCohomologyGerm (2 * p) P.rationalClassFin =
        T.relativeCohomologyGerm (2 * p)
          (RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hTP (Set.range f) (2 * p)
            P.rationalClassFin) :=
      (ConcreteCategory.congr_hom (P.relativeCohomologyGerm_restrict T hTP (2 * p))
        P.rationalClassFin).symm
    _ = T.relativeCohomologyGerm (2 * p) T.rationalClassFin := by
      rw [P.rationalClassFin_restrict T hTP rfl]
    _ = T.relativeCohomologyGerm (2 * p)
        (RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hTQ (Set.range f) (2 * p)
          Q.rationalClassFin) := by rw [hclass]
    _ = Q.relativeCohomologyGerm (2 * p) Q.rationalClassFin :=
      ConcreteCategory.congr_hom (Q.relativeCohomologyGerm_restrict T hTQ (2 * p))
        Q.rationalClassFin

/-- Actual differentiability of both ambient charts supplies the transition
hypothesis of germ invariance. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_germ_eq_of_charts
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ))) :
    P.relativeCohomologyGerm (2 * p) P.rationalClassFin =
      Q.relativeCohomologyGerm (2 * p) Q.rationalClassFin :=
  P.rationalClassFin_germ_eq_of_transition Q (P.transition_mdifferentiable Q hP hQ)

end Analytic.ImmersionNormalPair

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalTransition
