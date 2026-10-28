import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.CenterEndpointFibers

/-! # Deformation One Betti -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationOneBetti.BundleCycles

noncomputable section

/-! The graph-center one endpoint is exactly the graph followed by the
actual ambient evaluation section. Its Betti comparison with the special
endpoint follows from the already constructed center-family homotopy. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphDeformationOneOver : Conormal.BundleCycles.graphAmbientOver f ⟶ DeformationTopology.BundleCycles.graphDeformationOver f :=
  Over.homMk (Global.DeformationOneSection.BundleCycles.globalDeformationOneSection (OpenAmbient.BundleCycles.graph f).ker) (by
    change Global.DeformationOneSection.BundleCycles.globalDeformationOneSection (OpenAmbient.BundleCycles.graph f).ker ≫
      (Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f) = Chow.BundleCycles.graphAmbientStructureMap f
    rw [← Category.assoc, Global.DeformationOneSection.BundleCycles.globalDeformationOneSection_projection, Category.id_comp])

def graphPuncturedOneOver : Conormal.BundleCycles.graphAmbientOver f ⟶ CenterEndpointFibers.BundleCycles.graphPuncturedOver f :=
  Over.homMk (Global.DeformationOneFiber.BundleCycles.globalDeformationOnePunctured (OpenAmbient.BundleCycles.graph f).ker) (by
    change Global.DeformationOneFiber.BundleCycles.globalDeformationOnePunctured (OpenAmbient.BundleCycles.graph f).ker ≫
      (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker ≫
        (Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f)) = Chow.BundleCycles.graphAmbientStructureMap f
    rw [← Category.assoc, Global.DeformationOneFiber.BundleCycles.globalDeformationOnePunctured_inclusion,
      ← Category.assoc, Global.DeformationOneSection.BundleCycles.globalDeformationOneSection_projection, Category.id_comp])

theorem graphPuncturedOneOver_inclusion :
    graphPuncturedOneOver f ≫ CenterEndpointFibers.BundleCycles.graphPuncturedInclusionOver f = graphDeformationOneOver f :=
  Over.OverMorphism.ext (Global.DeformationOneFiber.BundleCycles.globalDeformationOnePunctured_inclusion (OpenAmbient.BundleCycles.graph f).ker)

theorem graphCenterEndpoint_one_graph :
    CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoint f 1 = Conormal.BundleCycles.graphOver f ≫ graphDeformationOneOver f := by
  apply Over.OverMorphism.ext
  have h := Global.DeformationOneFiber.BundleCycles.globalDeformation_one_factorization (OpenAmbient.BundleCycles.graph f).ker (CenterEndpointFibers.BundleCycles.graphCenterEndpointMap f 1)
    (Global.CenterFamilyParameter.BundleCycles.graphCenterFamilyEndpoint_one_parameter f)
  have hc : CenterEndpointFibers.BundleCycles.graphCenterEndpointMap f 1 ≫ Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker = OpenAmbient.BundleCycles.graph f :=
    congrArg Over.Hom.left (CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoint_toAmbient f 1)
  exact h.trans (congrArg (fun k => k ≫ Global.DeformationOneSection.BundleCycles.globalDeformationOneSection (OpenAmbient.BundleCycles.graph f).ker) hc)

theorem graphCenterPuncturedEndpoint_graph :
    CenterEndpointFibers.BundleCycles.graphCenterPuncturedEndpoint f = OpenAmbient.BundleCycles.graph f ≫ Global.DeformationOneFiber.BundleCycles.globalDeformationOnePunctured (OpenAmbient.BundleCycles.graph f).ker := by
  apply (cancel_mono (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker)).mp
  rw [CenterEndpointFibers.BundleCycles.graphCenterPuncturedEndpoint_toDeformation, Category.assoc, Global.DeformationOneFiber.BundleCycles.globalDeformationOnePunctured_inclusion]
  exact congrArg Over.Hom.left (graphCenterEndpoint_one_graph f)

theorem graphCenterPuncturedEndpointOver_graph :
    CenterEndpointFibers.BundleCycles.graphCenterPuncturedEndpointOver f = Conormal.BundleCycles.graphOver f ≫ graphPuncturedOneOver f :=
  Over.OverMorphism.ext (graphCenterPuncturedEndpoint_graph f)

theorem graphDeformation_betti_endpoints {R : Type} [Ring R] (M : ModuleCat.{0} R) (n : ℕ) :
    Betti.Scheme.schemeBettiMap M n (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f) ≫
      Betti.Scheme.schemeBettiMap M n (CenterEndpointFibers.BundleCycles.graphCenterSpecialEndpointOver f) =
    Betti.Scheme.schemeBettiMap M n (graphDeformationOneOver f) ≫ Betti.Scheme.schemeBettiMap M n (Conormal.BundleCycles.graphOver f) := by
  rw [← Conormal.BundleCycles.bettiMap_comp, CenterEndpointFibers.BundleCycles.graphCenterSpecialEndpointOver_toDeformation, ← Conormal.BundleCycles.bettiMap_comp,
    ← graphCenterEndpoint_one_graph]
  exact CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoints_betti_eq f M n

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationOneBetti.BundleCycles
