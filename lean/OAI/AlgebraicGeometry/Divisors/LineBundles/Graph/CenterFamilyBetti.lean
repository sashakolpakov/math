import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CenterDeformationIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationTopology
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.SectionBetti

/-! # Center Family Betti -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.CenterFamilyBetti.BundleCycles

noncomputable section

/-! The actual graph-center family is a morphism over the complex base.
Its zero and one endpoints induce identical Betti pullbacks in every degree. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphCenterFamilyOver : AffineLine.OverProduct.BundleCycles.affineLineOver X.toOver ⟶ DeformationTopology.BundleCycles.graphDeformationOver f :=
  Over.homMk (Global.CenterDeformationIso.BundleCycles.graphCenterFamily f) (by
    change Global.CenterDeformationIso.BundleCycles.graphCenterFamily f ≫
      (Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f) =
      AffineLine.Charts.BundleCycles.affineLineProjection X.carrier ≫ X.structureMap
    rw [← Category.assoc, Global.CenterDeformationIso.BundleCycles.graphCenterFamily_toBase, Category.assoc]
    exact congrArg (fun k => AffineLine.Charts.BundleCycles.affineLineProjection X.carrier ≫ k) (Conormal.BundleCycles.graphOver f).w)

def graphDeformationToAmbientOver : DeformationTopology.BundleCycles.graphDeformationOver f ⟶ Conormal.BundleCycles.graphAmbientOver f :=
  Over.homMk (Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker) rfl

theorem graphCenterFamilyOver_toAmbient :
    graphCenterFamilyOver f ≫ graphDeformationToAmbientOver f =
      AffineLine.PointFamily.BundleCycles.affineLineFirstOver X.toOver ≫ Conormal.BundleCycles.graphOver f :=
  Over.OverMorphism.ext (Global.CenterDeformationIso.BundleCycles.graphCenterFamily_toBase f)

def graphCenterFamilyEndpoint (a : ℂ) : X.toOver ⟶ DeformationTopology.BundleCycles.graphDeformationOver f :=
  AffineLine.ConstantSections.BundleCycles.affineLineConstantSectionOver X.toOver a ≫ graphCenterFamilyOver f

theorem graphCenterFamilyEndpoint_toAmbient (a : ℂ) :
    graphCenterFamilyEndpoint f a ≫ graphDeformationToAmbientOver f = Conormal.BundleCycles.graphOver f := by
  have hs : AffineLine.ConstantSections.BundleCycles.affineLineConstantSectionOver X.toOver a ≫ AffineLine.PointFamily.BundleCycles.affineLineFirstOver X.toOver = 𝟙 X.toOver :=
    Over.OverMorphism.ext (AffineLine.ConstantSections.BundleCycles.affineLineConstantSection_over X.toOver a)
  unfold graphCenterFamilyEndpoint
  rw [Category.assoc, graphCenterFamilyOver_toAmbient, ← Category.assoc, hs, Category.id_comp]

theorem graphCenterFamilyEndpoints_betti_eq {R : Type} [Ring R] (M : ModuleCat.{0} R) (n : ℕ) :
    Betti.Scheme.schemeBettiMap M n (graphCenterFamilyEndpoint f 0) =
      Betti.Scheme.schemeBettiMap M n (graphCenterFamilyEndpoint f 1) :=
  AffineLine.SectionBetti.BundleCycles.affineLineFamily_endpoints_betti_eq (graphCenterFamilyOver f) M n

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.CenterFamilyBetti.BundleCycles
