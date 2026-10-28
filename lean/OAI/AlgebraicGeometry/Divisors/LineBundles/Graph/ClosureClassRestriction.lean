import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.GradedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ExtensionClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationDimensions

/-! # Closure Class Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ClosureClassRestriction.BundleCycles

noncomputable section

section

/-! The class of the closure of the full graph-deformation family restricts to the genuine punctured pullback class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphDeformationCycleClosure (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Chow.BundleCycles.graphAmbientStructureMap f) d →₀ ℚ) →ₗ[ℚ]
      (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (DeformationTopology.BundleCycles.graphDeformationOver f).hom (d + 1) →₀ ℚ) :=
  (Open.CycleRestriction.BundleCycles.openDimensionCycleExtension (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker)
    (DeformationTopology.BundleCycles.graphDeformationOver f).hom (d + 1)).comp
      (Global.SpecializationComparison.BundleCycles.puncturedSpecializationCycleInput (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f) d)

variable [IsIntegral X.carrier] [IsIntegral Y.carrier] (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Chow.BundleCycles.graphAmbientStructureMap f))

include hd in
theorem graphClosure_codimension :
    (d + 1) + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (DeformationTopology.BundleCycles.graphDeformationOver f).hom := by
  rw [DeformationDimensions.BundleCycles.graphDeformation_dimension]
  change (d + 1) + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Chow.BundleCycles.graphAmbientStructureMap f) + 1
  omega

theorem graphPuncturedInput_absoluteClass (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Chow.BundleCycles.graphAmbientStructureMap f) d →₀ ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (PuncturedClass.BundleCycles.graphPuncturedProjectionOver f)
      (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (Conormal.BundleCycles.graphAmbientOver f) d p hd c) =
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (CenterEndpointFibers.BundleCycles.graphPuncturedOver f) (d + 1) p (DeformationDimensions.BundleCycles.graphPunctured_codimension f d p hd)
      (Global.SpecializationComparison.BundleCycles.puncturedSpecializationCycleInput (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f) d c) :=
  @Punctured.GradedClass.BundleCycles.schemeGradedAbsoluteClass_puncturedInput (Conormal.BundleCycles.graphAmbientOver f) (OpenAmbient.BundleCycles.graph f).ker
    (IntegralDeformation.BundleCycles.graphAmbientOver_integral f) inferInstance inferInstance (DeformationTopology.BundleCycles.graphAmbientOver_metrizable f)
    (PuncturedClass.BundleCycles.graphPuncturedOver_integral f) (PuncturedClass.BundleCycles.graphPuncturedOver_smooth f)
    (PuncturedClass.BundleCycles.graphPuncturedOver_noetherian f) (PuncturedClass.BundleCycles.graphPuncturedOver_metrizable f)
    d p hd (DeformationDimensions.BundleCycles.graphPunctured_codimension f d p hd) c

theorem graphClosure_absoluteClass_restrict (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Chow.BundleCycles.graphAmbientStructureMap f) d →₀ ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (CenterEndpointFibers.BundleCycles.graphPuncturedInclusionOver f)
      (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (DeformationTopology.BundleCycles.graphDeformationOver f) (d + 1) p (graphClosure_codimension f d p hd)
        (graphDeformationCycleClosure f d c)) =
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (CenterEndpointFibers.BundleCycles.graphPuncturedOver f) (d + 1) p (DeformationDimensions.BundleCycles.graphPunctured_codimension f d p hd)
      (Global.SpecializationComparison.BundleCycles.puncturedSpecializationCycleInput (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f) d c) := by
  exact Open.ExtensionClass.BundleCycles.schemeGradedAbsoluteClass_openExtension (CenterEndpointFibers.BundleCycles.graphPuncturedInclusionOver f) (d + 1) p
    (graphClosure_codimension f d p hd)
    (Global.SpecializationComparison.BundleCycles.puncturedSpecializationCycleInput (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f) d c)

end

/-! The actual parameter-one section pulls the class of the complete deformation closure back to the original cycle class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier] [IsIntegral Y.carrier]
  (f : X.toOver ⟶ Y.toOver) (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Chow.BundleCycles.graphAmbientStructureMap f))

theorem graphDeformationOne_absoluteCycleClass
    (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Chow.BundleCycles.graphAmbientStructureMap f) d →₀ ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (DeformationOneBetti.BundleCycles.graphDeformationOneOver f)
      (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (DeformationTopology.BundleCycles.graphDeformationOver f) (d + 1) p (graphClosure_codimension f d p hd)
        (graphDeformationCycleClosure f d c)) =
      Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (Conormal.BundleCycles.graphAmbientOver f) d p hd c := by
  let a := Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (DeformationTopology.BundleCycles.graphDeformationOver f) (d + 1) p
    (graphClosure_codimension f d p hd) (graphDeformationCycleClosure f d c)
  let b := Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (Conormal.BundleCycles.graphAmbientOver f) d p hd c
  have hm : Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (DeformationOneBetti.BundleCycles.graphDeformationOneOver f) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (CenterEndpointFibers.BundleCycles.graphPuncturedInclusionOver f) ≫
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (DeformationOneBetti.BundleCycles.graphPuncturedOneOver f) :=
    (congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p)) (DeformationOneBetti.BundleCycles.graphPuncturedOneOver_inclusion f).symm).trans
      (Conormal.BundleCycles.bettiMap_comp (ModuleCat.of ℚ ℚ) (2 * p) (DeformationOneBetti.BundleCycles.graphPuncturedOneOver f) (CenterEndpointFibers.BundleCycles.graphPuncturedInclusionOver f))
  have hc : Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (CenterEndpointFibers.BundleCycles.graphPuncturedInclusionOver f) a =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (PuncturedClass.BundleCycles.graphPuncturedProjectionOver f) b :=
    (graphClosure_absoluteClass_restrict f d p hd c).trans (graphPuncturedInput_absoluteClass f d p hd c).symm
  have hi : Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (PuncturedClass.BundleCycles.graphPuncturedProjectionOver f) ≫
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (DeformationOneBetti.BundleCycles.graphPuncturedOneOver f) =
      𝟙 (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) (Conormal.BundleCycles.graphAmbientOver f) (2 * p)) := by
    rw [← Conormal.BundleCycles.bettiMap_comp, PuncturedClass.BundleCycles.graphPuncturedOneOver_projection, Conormal.BundleCycles.bettiMap_id]
  exact (ConcreteCategory.congr_hom hm a).trans
    ((congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (DeformationOneBetti.BundleCycles.graphPuncturedOneOver f)) hc).trans
      (ConcreteCategory.congr_hom hi b))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ClosureClassRestriction.BundleCycles
