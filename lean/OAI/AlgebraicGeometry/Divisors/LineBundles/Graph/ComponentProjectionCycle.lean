import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentProjectionLift
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponentCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFundamentalCycle

/-! # Component Projection Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentProjectionCycle.BundleCycles

noncomputable section

/-! Restricting the full projection cycle to the actual source and receiving target components gives their full projection cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem graphProjectionPointPullback_integral_single {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    [IsIntegral X.carrier] (f : X.toOver ⟶ Y.toOver) (y : Y.carrier) (r : ℚ) :
    Chow.BundleCycles.graphProjectionPointPullback f (Finsupp.single y r) =
      Finsupp.single (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (OpenAmbient.BundleCycles.graphSecondProjection f) y) r := by
  change FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback (OpenAmbient.BundleCycles.graphSecondProjection f) (Finsupp.single y r) = _
  rw [Integral.FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback_eq_integralFiberCycleExtension]
  exact Finsupp.mapDomain_single

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (C : irreducibleComponents X.carrier)

theorem graphProjectionPointPullback_component (z : Y.carrier →₀ ℚ) :
    Finsupp.comapDomain (ComponentAmbient.BundleCycles.graphComponentAmbientMap f C) (Chow.BundleCycles.graphProjectionPointPullback f z)
      (ComponentAmbient.BundleCycles.graphComponentAmbientMap f C).isOpenEmbedding.injective.injOn =
      Chow.BundleCycles.graphProjectionPointPullback (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)
        (Finsupp.comapDomain (Y.componentInclusion (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)) z
          (Y.componentInclusion (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)).isOpenEmbedding.injective.injOn) := by
  classical
  let j := ComponentAmbient.BundleCycles.graphComponentAmbientMap f C
  let b := Y.componentInclusion (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)
  let L : (OpenAmbient.BundleCycles.graphAmbient f →₀ ℚ) →ₗ[ℚ] (OpenAmbient.BundleCycles.graphAmbient (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C) →₀ ℚ) :=
    Finsupp.lcomapDomain j j.isOpenEmbedding.injective
  let B : (Y.carrier →₀ ℚ) →ₗ[ℚ] ((Y.componentVariety (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)).carrier →₀ ℚ) :=
    Finsupp.lcomapDomain b b.isOpenEmbedding.injective
  change L (Chow.BundleCycles.graphProjectionPointPullback f z) = Chow.BundleCycles.graphProjectionPointPullback (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C) (B z)
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | single y r =>
    rw [ProjectionComponentCycle.BundleCycles.graphProjectionPointPullback_single, map_sum]
    by_cases hy : y ∈ Set.range b
    · obtain ⟨v, rfl⟩ := hy
      have hs : B (Finsupp.single (b v) r) = Finsupp.single v r :=
        Finsupp.comapDomain_single b v r b.isOpenEmbedding.injective.injOn
      rw [hs, graphProjectionPointPullback_integral_single]
      have hsum : (∑ D ∈ (Set.univ : Set (irreducibleComponents X.carrier)).toFinite.toFinset,
          L (Finsupp.single (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f D (b v)) r)) =
          L (Finsupp.single (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f C (b v)) r) := by
        apply Finset.sum_eq_single C
        · intro D _ hDC
          apply Finsupp.comapDomain_single_of_not_mem_range
          intro hm
          exact hDC ((ComponentProjectionLift.BundleCycles.graphComponentAmbientMap_componentPoint_mem_iff f C D (b v)).mp hm).1
        · intro hc
          exact False.elim (hc (by simp only [Set.Finite.mem_toFinset, Set.mem_univ]))
      exact hsum.trans
        ((congrArg (fun x => L (Finsupp.single x r)) (ComponentProjectionLift.BundleCycles.graphComponentAmbientMap_fiberGenericPoint f C v)).symm.trans
          (Finsupp.comapDomain_single j _ r j.isOpenEmbedding.injective.injOn))
    · have hs : B (Finsupp.single y r) = 0 := by
        apply Finsupp.comapDomain_single_of_not_mem_range
        exact hy
      rw [hs, map_zero]
      apply Finset.sum_eq_zero
      intro D _
      apply Finsupp.comapDomain_single_of_not_mem_range
      intro hm
      exact hy ((ComponentProjectionLift.BundleCycles.graphComponentAmbientMap_componentPoint_mem_iff f C D y).mp hm).2

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentProjectionCycle.BundleCycles
