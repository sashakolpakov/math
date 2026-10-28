import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CenterFamilyParameter
import OAI.AlgebraicGeometry.Divisors.LineBundles.ReducedClosedFactor

/-! # Center Endpoint Fibers -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.CenterEndpointFibers.BundleCycles

noncomputable section

section

/-! The actual center-family endpoints factor through the special fiber and
the punctured deformation, respectively. The special endpoint is a section
of the normal-cone projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphCenterEndpointMap (a : ℂ) : X.carrier ⟶ Global.Deformation.BundleCycles.globalDeformation (OpenAmbient.BundleCycles.graph f).ker :=
  (CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoint f a).left

theorem graphCenterEndpoint_zero_range :
    Set.range (graphCenterEndpointMap f 0) ⊆
      Set.range (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (OpenAmbient.BundleCycles.graph f).ker) := by
  rw [Global.Specialization.BundleCycles.globalSpecialFiberMap_range]
  rintro _ ⟨x, rfl⟩ hx
  have h := Scheme.preimage_basicOpen_top (graphCenterEndpointMap f 0)
    (Global.Specialization.BundleCycles.globalDeformationParameterSection (OpenAmbient.BundleCycles.graph f).ker)
  have ht : (graphCenterEndpointMap f 0).appTop (Global.Specialization.BundleCycles.globalDeformationParameterSection (OpenAmbient.BundleCycles.graph f).ker) = 0 :=
    Global.CenterFamilyParameter.BundleCycles.graphCenterFamilyEndpoint_zero_parameter f
  rw [ht, Scheme.basicOpen_zero] at h
  have hx' : x ∈ graphCenterEndpointMap f 0 ⁻¹ᵁ
      (Global.Deformation.BundleCycles.globalDeformation (OpenAmbient.BundleCycles.graph f).ker).basicOpen (Global.Specialization.BundleCycles.globalDeformationParameterSection (OpenAmbient.BundleCycles.graph f).ker) := hx
  rw [h] at hx'
  exact hx'

def graphCenterSpecialEndpoint : X.carrier ⟶ Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker :=
  ReducedClosedFactor.BundleCycles.reducedClosedFactor (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (OpenAmbient.BundleCycles.graph f).ker)
    (graphCenterEndpointMap f 0) (graphCenterEndpoint_zero_range f)

theorem graphCenterSpecialEndpoint_toDeformation :
    graphCenterSpecialEndpoint f ≫ Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (OpenAmbient.BundleCycles.graph f).ker =
      graphCenterEndpointMap f 0 :=
  ReducedClosedFactor.BundleCycles.reducedClosedFactor_comp _ _ _

theorem graphCenterSpecialEndpoint_toAmbient :
    graphCenterSpecialEndpoint f ≫ Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker = OpenAmbient.BundleCycles.graph f := by
  rw [← Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase, ← Category.assoc, graphCenterSpecialEndpoint_toDeformation]
  exact congrArg Over.Hom.left (CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoint_toAmbient f 0)

theorem graphCenterSpecialEndpoint_projection :
    graphCenterSpecialEndpoint f ≫ Chow.BundleCycles.graphNormalProjection f = 𝟙 X.carrier := by
  have h := congrArg (fun k => k ≫ OpenAmbient.BundleCycles.graphFirstProjection f) (graphCenterSpecialEndpoint_toAmbient f)
  rw [← Conormal.BundleCycles.graphNormalProjection_graph, Category.assoc, Category.assoc,
    OpenAmbient.BundleCycles.graph_firstProjection, Category.comp_id] at h
  exact h

theorem graphCenterEndpoint_one_range :
    Set.range (graphCenterEndpointMap f 1) ⊆
      Set.range (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker) := by
  change Set.range (graphCenterEndpointMap f 1) ⊆
    Set.range (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen (OpenAmbient.BundleCycles.graph f).ker).ι
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have h := Scheme.preimage_basicOpen_top (graphCenterEndpointMap f 1)
    (Global.Specialization.BundleCycles.globalDeformationParameterSection (OpenAmbient.BundleCycles.graph f).ker)
  have ht : (graphCenterEndpointMap f 1).appTop (Global.Specialization.BundleCycles.globalDeformationParameterSection (OpenAmbient.BundleCycles.graph f).ker) = 1 :=
    Global.CenterFamilyParameter.BundleCycles.graphCenterFamilyEndpoint_one_parameter f
  rw [ht, Scheme.basicOpen_one] at h
  change x ∈ graphCenterEndpointMap f 1 ⁻¹ᵁ
    (Global.Deformation.BundleCycles.globalDeformation (OpenAmbient.BundleCycles.graph f).ker).basicOpen (Global.Specialization.BundleCycles.globalDeformationParameterSection (OpenAmbient.BundleCycles.graph f).ker)
  rw [h]
  trivial

def graphCenterPuncturedEndpoint : X.carrier ⟶ Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured (OpenAmbient.BundleCycles.graph f).ker :=
  IsOpenImmersion.lift (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker)
    (graphCenterEndpointMap f 1) (graphCenterEndpoint_one_range f)

theorem graphCenterPuncturedEndpoint_toDeformation :
    graphCenterPuncturedEndpoint f ≫ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker =
      graphCenterEndpointMap f 1 :=
  IsOpenImmersion.lift_fac _ _ _

end

/-! The actual special and punctured endpoint factorizations yield a
commuting Betti square, for every coefficient module and every degree. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphSpecialFiberOver : Conormal.BundleCycles.graphConeOver f ⟶ DeformationTopology.BundleCycles.graphDeformationOver f :=
  Over.homMk (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (OpenAmbient.BundleCycles.graph f).ker) (by
    change Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (OpenAmbient.BundleCycles.graph f).ker ≫
      (Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f) = _
    rw [← Category.assoc, Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase]
    rfl)

def graphCenterSpecialEndpointOver : X.toOver ⟶ Conormal.BundleCycles.graphConeOver f :=
  Over.homMk (graphCenterSpecialEndpoint f) (by
    change graphCenterSpecialEndpoint f ≫ Chow.BundleCycles.graphConeStructureMap f = X.structureMap
    rw [← Chow.BundleCycles.graphConeStructureMap_normal, ← Category.assoc,
      graphCenterSpecialEndpoint_projection, Category.id_comp])

theorem graphCenterSpecialEndpointOver_projection :
    graphCenterSpecialEndpointOver f ≫ Conormal.BundleCycles.graphNormalProjectionOver f = 𝟙 X.toOver :=
  Over.OverMorphism.ext (graphCenterSpecialEndpoint_projection f)

theorem graphCenterSpecialEndpointOver_toDeformation :
    graphCenterSpecialEndpointOver f ≫ graphSpecialFiberOver f = CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoint f 0 :=
  Over.OverMorphism.ext (graphCenterSpecialEndpoint_toDeformation f)

def graphPuncturedOver : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker ≫ (DeformationTopology.BundleCycles.graphDeformationOver f).hom)

def graphPuncturedInclusionOver : graphPuncturedOver f ⟶ DeformationTopology.BundleCycles.graphDeformationOver f :=
  Over.homMk (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker) rfl

def graphCenterPuncturedEndpointOver : X.toOver ⟶ graphPuncturedOver f :=
  Over.homMk (graphCenterPuncturedEndpoint f) (by
    change graphCenterPuncturedEndpoint f ≫
      (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker ≫
        (Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f)) = X.structureMap
    rw [← Category.assoc, graphCenterPuncturedEndpoint_toDeformation]
    exact (CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoint f 1).w)

theorem graphCenterPuncturedEndpointOver_toDeformation :
    graphCenterPuncturedEndpointOver f ≫ graphPuncturedInclusionOver f = CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoint f 1 :=
  Over.OverMorphism.ext (graphCenterPuncturedEndpoint_toDeformation f)

theorem graphEndpoint_betti_square {R : Type} [Ring R] (M : ModuleCat.{0} R) (n : ℕ) :
    Betti.Scheme.schemeBettiMap M n (graphSpecialFiberOver f) ≫
      Betti.Scheme.schemeBettiMap M n (graphCenterSpecialEndpointOver f) =
    Betti.Scheme.schemeBettiMap M n (graphPuncturedInclusionOver f) ≫
      Betti.Scheme.schemeBettiMap M n (graphCenterPuncturedEndpointOver f) := by
  rw [← Conormal.BundleCycles.bettiMap_comp, ← Conormal.BundleCycles.bettiMap_comp, graphCenterSpecialEndpointOver_toDeformation,
    graphCenterPuncturedEndpointOver_toDeformation]
  exact CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoints_betti_eq f M n

theorem graphCenterSpecialEndpoint_betti_retraction {R : Type} [Ring R]
    (M : ModuleCat.{0} R) (n : ℕ) :
    Betti.Scheme.schemeBettiMap M n (Conormal.BundleCycles.graphNormalProjectionOver f) ≫
      Betti.Scheme.schemeBettiMap M n (graphCenterSpecialEndpointOver f) = 𝟙 (Betti.Scheme.schemeBetti M X.toOver n) := by
  rw [← Conormal.BundleCycles.bettiMap_comp, graphCenterSpecialEndpointOver_projection, Conormal.BundleCycles.bettiMap_id]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.CenterEndpointFibers.BundleCycles
