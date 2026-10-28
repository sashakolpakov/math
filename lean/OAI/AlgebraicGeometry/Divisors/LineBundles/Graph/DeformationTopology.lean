import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationSmooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Conormal
import OAI.AlgebraicGeometry.CycleClass.Thom.SeparatedSchemeTopology

/-! # Deformation Topology -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationTopology.BundleCycles

noncomputable section

/-! The actual graph deformation and normal cone have metrizable
ordinary complex point spaces, from their separated finite-type structures. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphDeformationOver : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f)

instance graphAmbientStructureMap_isProper : IsProper (Chow.BundleCycles.graphAmbientStructureMap f) := by
  let : IsProper X.structureMap := X.projective.isProper
  rw [← Chow.BundleCycles.graphAmbientStructureMap_first]
  infer_instance

instance graphDeformationOver_smooth : Smooth (graphDeformationOver f).hom :=
  DeformationSmooth.BundleCycles.graphDeformationStructure_smooth f

instance graphDeformationOver_metrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphDeformationOver f)) := by
  let : IsSeparated (graphDeformationOver f).hom := by
    change IsSeparated (Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f)
    infer_instance
  let : QuasiCompact (graphDeformationOver f).hom := by
    change QuasiCompact (Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f)
    infer_instance
  exact CycleClass.Thom.SeparatedSchemeTopology.Constructions.schemePoints_metrizable (graphDeformationOver f)

instance graphAmbientOver_metrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Conormal.BundleCycles.graphAmbientOver f)) := by
  let : IsProper (Conormal.BundleCycles.graphAmbientOver f).hom := graphAmbientStructureMap_isProper f
  let : LocallyOfFiniteType (Conormal.BundleCycles.graphAmbientOver f).hom := Chow.BundleCycles.graphAmbientStructureMap_locallyOfFiniteType f
  exact CycleClass.Thom.SeparatedSchemeTopology.Constructions.schemePoints_metrizable (Conormal.BundleCycles.graphAmbientOver f)

instance graphConeOver_metrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Conormal.BundleCycles.graphConeOver f)) := by
  let : IsSeparated (Conormal.BundleCycles.graphConeOver f).hom := by
    change IsSeparated (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f)
    rw [← Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase]
    infer_instance
  let : QuasiCompact (Conormal.BundleCycles.graphConeOver f).hom := by
    change QuasiCompact (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f)
    infer_instance
  let : LocallyOfFiniteType (Conormal.BundleCycles.graphConeOver f).hom := Conormal.BundleCycles.graphConeStructureMap_locallyOfFiniteType f
  exact CycleClass.Thom.SeparatedSchemeTopology.Constructions.schemePoints_metrizable (Conormal.BundleCycles.graphConeOver f)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationTopology.BundleCycles
