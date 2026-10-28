import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberOpenCycleClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecialFiberSection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationComparison

/-! # Specialization Cycle Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationCycleClass.BundleCycles

noncomputable section

/-! Canonical classes commute with the actual full graph-deformation specialization: closing the punctured family and restricting its class gives the class of the constructed specialization cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier] [IsIntegral Y.carrier]
  (f : X.toOver ⟶ Y.toOver) (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Conormal.BundleCycles.graphConeOver f).hom)

theorem graphSpecialization_absoluteCycleClass
    (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Chow.BundleCycles.graphAmbientStructureMap f) d →₀ ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f)
      (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (DeformationTopology.BundleCycles.graphDeformationOver f) (d + 1) p
        (Principal.FiberOpenCycleClass.BundleCycles.principalFiberClosure_codimension (SpecialFiberSection.BundleCycles.graphSpecialFiber_nativeCodimension f) d p hd)
        (Open.CycleRestriction.BundleCycles.openDimensionCycleExtension (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker)
          (DeformationTopology.BundleCycles.graphDeformationOver f).hom (d + 1)
          (Global.SpecializationComparison.BundleCycles.puncturedSpecializationCycleInput (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f) d c))) =
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (Conormal.BundleCycles.graphConeOver f) d p hd
      (Graded.GlobalSpecialization.BundleCycles.globalGradedCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f) d c) := by
  let I := (OpenAmbient.BundleCycles.graph f).ker
  have hj : Set.range (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) ⊆
      (Global.Deformation.BundleCycles.globalDeformation I).basicOpen (Global.Specialization.BundleCycles.globalDeformationParameterSection I) :=
    (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I).range_ι.subset
  have h := @Principal.FiberOpenCycleClass.BundleCycles.principalFiber_absoluteClass_openExtension
    (Conormal.BundleCycles.graphConeOver f) (DeformationTopology.BundleCycles.graphDeformationOver f)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f) inferInstance
    (Global.Specialization.BundleCycles.globalDeformationParameterSection I) (Global.Specialization.BundleCycles.globalSpecialFiberMap_range I) (SpecialFiberSection.BundleCycles.graphSpecialFiber_nativeCodimension f)
    (SpecialFiberSection.BundleCycles.graphSpecialFiber_principal_affineNeighborhoods f)
    (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I) inferInstance (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)
    (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion_isOpenImmersion I) hj d p hd
    (Global.SpecializationComparison.BundleCycles.puncturedSpecializationCycleInput I (Chow.BundleCycles.graphAmbientStructureMap f) d c)
  have hc : DimensionChow.BundleCycles.dimensionCycleTransport (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f).w d
      (Principal.CartierFiber.BundleCycles.principalCartierFiberCycleMap (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f).left (Global.Specialization.BundleCycles.globalDeformationParameterSection I)
        (DeformationTopology.BundleCycles.graphDeformationOver f).hom d
        (Open.CycleRestriction.BundleCycles.openDimensionCycleExtension (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (DeformationTopology.BundleCycles.graphDeformationOver f).hom (d + 1)
          (Global.SpecializationComparison.BundleCycles.puncturedSpecializationCycleInput I (Chow.BundleCycles.graphAmbientStructureMap f) d c))) =
      Graded.GlobalSpecialization.BundleCycles.globalGradedCycleSpecialization I (Chow.BundleCycles.graphAmbientStructureMap f) d c :=
    Global.SpecializationComparison.BundleCycles.globalGradedCycleSpecialization_eq_deformation I (Chow.BundleCycles.graphAmbientStructureMap f) d c
  exact h.trans (congrArg (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (Conormal.BundleCycles.graphConeOver f) d p hd) hc)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationCycleClass.BundleCycles
