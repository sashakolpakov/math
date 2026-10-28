import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ClosureClassRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationCycleClass

/-! # Specialization Betti Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationBettiClass.BundleCycles

noncomputable section

/-! The two actual graph-deformation endpoints identify the class of the full specialization cycle with graph pullback after restricting along the normal-cone center section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier] [IsIntegral Y.carrier]
  (f : X.toOver ⟶ Y.toOver) (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Chow.BundleCycles.graphAmbientStructureMap f))

include hd in
theorem graphSpecialization_codimension : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Conormal.BundleCycles.graphConeOver f).hom :=
  hd.trans (DeformationDimensions.BundleCycles.graphCone_dimension_eq_ambient f).symm

theorem graphSpecialization_center_absoluteClass
    (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Chow.BundleCycles.graphAmbientStructureMap f) d →₀ ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (CenterEndpointFibers.BundleCycles.graphCenterSpecialEndpointOver f)
      (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (Conormal.BundleCycles.graphConeOver f) d p (graphSpecialization_codimension f d p hd)
        (Graded.GlobalSpecialization.BundleCycles.globalGradedCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f) d c)) =
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (Conormal.BundleCycles.graphOver f)
      (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (Conormal.BundleCycles.graphAmbientOver f) d p hd c) := by
  let a : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) (DeformationTopology.BundleCycles.graphDeformationOver f) (2 * p) :=
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (DeformationTopology.BundleCycles.graphDeformationOver f) (d + 1) p
    (ClosureClassRestriction.BundleCycles.graphClosure_codimension f d p hd) (ClosureClassRestriction.BundleCycles.graphDeformationCycleClosure f d c)
  let s : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) (Conormal.BundleCycles.graphConeOver f) (2 * p) →ₗ[ℚ]
      Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X.toOver (2 * p) :=
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (CenterEndpointFibers.BundleCycles.graphCenterSpecialEndpointOver f)).hom
  let g : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) (Conormal.BundleCycles.graphAmbientOver f) (2 * p) →ₗ[ℚ]
      Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X.toOver (2 * p) :=
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (Conormal.BundleCycles.graphOver f)).hom
  have hs : Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f) a =
      Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (Conormal.BundleCycles.graphConeOver f) d p (graphSpecialization_codimension f d p hd)
        (Graded.GlobalSpecialization.BundleCycles.globalGradedCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f) d c) :=
    SpecializationCycleClass.BundleCycles.graphSpecialization_absoluteCycleClass f d p (graphSpecialization_codimension f d p hd) c
  have he : s (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f) a) =
      g (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (DeformationOneBetti.BundleCycles.graphDeformationOneOver f) a) :=
    ConcreteCategory.congr_hom (DeformationOneBetti.BundleCycles.graphDeformation_betti_endpoints f (ModuleCat.of ℚ ℚ) (2 * p)) a
  exact (congrArg s hs).symm.trans
    (he.trans (congrArg g
      (ClosureClassRestriction.BundleCycles.graphDeformationOne_absoluteCycleClass f d p hd c)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationBettiClass.BundleCycles
