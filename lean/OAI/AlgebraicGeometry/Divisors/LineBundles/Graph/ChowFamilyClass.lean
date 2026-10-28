import OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationFiberClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProductClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationChowClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.GraphPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFundamentalCycle

/-! # Chow Family Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ChowFamilyClass.BundleCycles

noncomputable section

section

/-! The actual projection and normal-bundle Chow families have their canonical Betti cycle-class comparisons in every complementary dimension grade. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier] [IsIntegral Y.carrier]
  (f : X.toOver ⟶ Y.toOver) (p e : ℕ)

omit [AlgebraicGeometry.IsIntegral Y.carrier] in
theorem graphNormalChowFamily_cycleClass
    (he : e + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Conormal.BundleCycles.graphConeOver f).hom) (a : Chow.BundleCycles.ChowQ X p) :
    Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass (Conormal.BundleCycles.graphConeOver f) e p he (GraphNormal.ChowFamily.BundleCycles.graphNormalChowFamily f p e a) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (Conormal.BundleCycles.graphNormalProjectionOver f) (Geometric.CycleClass.BundleCycles.geometricCycleClassQ X p a) := by
  obtain ⟨z, rfl⟩ := Chow.BundleCycles.cycleToChowQ_surjective X p a
  rw [GraphNormal.ChowFamily.BundleCycles.graphNormalChowFamily_cycle, Geometric.CycleClass.BundleCycles.geometricCycleClassQ_cycle]
  exact PresentationFiberClass.BundleCycles.presentationFiberPointChow_class X (Conormal.BundleCycles.graphNormalProjectionOver f) (ProductClass.BundleCycles.graphNormalOpenProductChart f) e p he z

theorem graphProjectionChowFamily_cycleClass
    (he : e + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Chow.BundleCycles.graphAmbientStructureMap f)) (a : Chow.BundleCycles.ChowQ Y p) :
    Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass (Conormal.BundleCycles.graphAmbientOver f) e p he (ProjectionChowFamily.BundleCycles.graphProjectionChowFamily f p e a) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (Conormal.BundleCycles.graphSecondProjectionOver f) (Geometric.CycleClass.BundleCycles.geometricCycleClassQ Y p a) := by
  obtain ⟨z, rfl⟩ := Chow.BundleCycles.cycleToChowQ_surjective Y p a
  rw [ProjectionChowFamily.BundleCycles.graphProjectionChowFamily_cycle, Geometric.CycleClass.BundleCycles.geometricCycleClassQ_cycle]
  change Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass (Conormal.BundleCycles.graphAmbientOver f) e p he
    (Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphAmbientStructureMap f) e (FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback (OpenAmbient.BundleCycles.graphSecondProjection f) (Chow.BundleCycles.pointCycle Y p z))) = _
  rw [Integral.FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback_eq_integralFiberCycleExtension]
  exact PresentationFiberClass.BundleCycles.presentationFiberPointChow_class Y (Conormal.BundleCycles.graphSecondProjectionOver f) (ProductClass.BundleCycles.graphProjectionOpenProductChart f) e p he z

end

/-! The actual graph Chow pullback commutes with the independently constructed geometric cycle class for every morphism between integral presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier] [IsIntegral Y.carrier]
  (f : X.toOver ⟶ Y.toOver) (p : ℕ)

theorem graphChowPullback_cycleClass_of_grade (e : ℕ)
    (he : e + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Chow.BundleCycles.graphAmbientStructureMap f)) (a : Chow.BundleCycles.ChowQ Y p) :
    Geometric.CycleClass.BundleCycles.geometricCycleClassQ X p (ChowPullback.BundleCycles.graphChowPullback f p a) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (Geometric.CycleClass.BundleCycles.geometricCycleClassQ Y p a) := by
  let hN := SpecializationBettiClass.BundleCycles.graphSpecialization_codimension f e p he
  let N := Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass (Conormal.BundleCycles.graphConeOver f) e p hN
  let s : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) (Conormal.BundleCycles.graphConeOver f) (p + p) →ₗ[ℚ]
      X.rationalCohomology (p + p) :=
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (CenterEndpointFibers.BundleCycles.graphCenterSpecialEndpointOver f)).hom
  let g : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) (Conormal.BundleCycles.graphAmbientOver f) (p + p) →ₗ[ℚ]
      X.rationalCohomology (p + p) :=
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (Conormal.BundleCycles.graphOver f)).hom
  have hn := graphNormalChowFamily_cycleClass f p e hN (ChowPullback.BundleCycles.graphChowPullback f p a)
  have hq := congrArg N (Geometric.GraphPullback.BundleCycles.graphChowPullback_graphEquation f p a e)
  have hs := SpecializationChowClass.BundleCycles.graphSpecialization_center_chowClass f e p he (ProjectionChowFamily.BundleCycles.graphProjectionChowFamily f p e a)
  have hp := graphProjectionChowFamily_cycleClass f p e he a
  have hr := ConcreteCategory.congr_hom
    (CenterEndpointFibers.BundleCycles.graphCenterSpecialEndpoint_betti_retraction f (ModuleCat.of ℚ ℚ) (p + p))
      (Geometric.CycleClass.BundleCycles.geometricCycleClassQ X p (ChowPullback.BundleCycles.graphChowPullback f p a))
  have hg := ConcreteCategory.congr_hom (Conormal.BundleCycles.graphBetti_factorization f (p + p)) (Geometric.CycleClass.BundleCycles.geometricCycleClassQ Y p a)
  exact hr.symm.trans ((congrArg s hn).symm.trans
    ((congrArg s hq).trans (hs.trans ((congrArg g hp).trans hg.symm))))

theorem graphChowPullback_cycleClass_integral (a : Chow.BundleCycles.ChowQ Y p) :
    Geometric.CycleClass.BundleCycles.geometricCycleClassQ X p (ChowPullback.BundleCycles.graphChowPullback f p a) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (Geometric.CycleClass.BundleCycles.geometricCycleClassQ Y p a) := by
  by_cases hp : p ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.structureMap
  · have hdim := Projection.SupportDimension.BundleCycles.productPresentation_dimension X.toOver Y.toOver (Conormal.BundleCycles.graphAmbientOver f)
      (Conormal.BundleCycles.graphFirstProjectionOver f) (Conormal.BundleCycles.graphSecondProjectionOver f) (ProductClass.BundleCycles.graphAmbient_productIsLimit f)
    have hle : p ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Chow.BundleCycles.graphAmbientStructureMap f) := by
      change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Chow.BundleCycles.graphAmbientStructureMap f) =
        Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap + Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.structureMap at hdim
      omega
    exact graphChowPullback_cycleClass_of_grade f p
      (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Chow.BundleCycles.graphAmbientStructureMap f) - p) (Nat.sub_add_cancel hle) a
  · obtain ⟨z, rfl⟩ := Chow.BundleCycles.cycleToChowQ_surjective Y p a
    have hz : z = 0 := by
      ext Z
      have hd := PresentationComponentSupportClass.BundleCycles.integralPresentationSupport_dimension Y p Z
      exact False.elim (hp (by omega))
    subst z
    simp only [map_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ChowFamilyClass.BundleCycles
