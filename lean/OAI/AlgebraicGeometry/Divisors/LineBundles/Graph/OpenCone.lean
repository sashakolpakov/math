import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SpecialFiberIdentifiedIdeal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Chow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen

/-! # Open Cone -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenCone.BundleCycles

noncomputable section

/-! The actual graph normal cone restricts along open source and target maps, and its full fiber extension and specialization cycles retain all coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y X' Y' : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (g : X'.toOver ⟶ Y'.toOver)
    (a : X'.toOver ⟶ X.toOver) (b : Y'.toOver ⟶ Y.toOver)
    [IsOpenImmersion a.left] [IsOpenImmersion b.left] (h : a ≫ f = g ≫ b)

def graphOpenConeMap : Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph g).ker ⟶ Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker :=
  Open.SpecialFiberIdentifiedIdeal.BundleCycles.globalOpenSpecialFiberWithIdeal (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b) (OpenAmbient.BundleCycles.graph f).ker (OpenAmbient.BundleCycles.graph g).ker
    (OpenSquare.BundleCycles.graphOpenAmbientMap_kernel f g a b h)

instance graphOpenConeMap_open : IsOpenImmersion (graphOpenConeMap f g a b h) :=
  Open.SpecialFiberIdentifiedIdeal.BundleCycles.globalOpenSpecialFiberWithIdeal_open (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b) (OpenAmbient.BundleCycles.graph f).ker (OpenAmbient.BundleCycles.graph g).ker
    (OpenSquare.BundleCycles.graphOpenAmbientMap_kernel f g a b h)

theorem graphOpenConeMap_toAmbient :
    graphOpenConeMap f g a b h ≫ Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker =
      Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph g).ker ≫ OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b :=
  Open.SpecialFiberIdentifiedIdeal.BundleCycles.globalOpenSpecialFiberWithIdeal_toBase (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b) (OpenAmbient.BundleCycles.graph f).ker (OpenAmbient.BundleCycles.graph g).ker
    (OpenSquare.BundleCycles.graphOpenAmbientMap_kernel f g a b h)

theorem graphOpenConeMap_normal :
    graphOpenConeMap f g a b h ≫ Chow.BundleCycles.graphNormalProjection f = Chow.BundleCycles.graphNormalProjection g ≫ a.left := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ OpenAmbient.BundleCycles.graphFirstProjection f) (graphOpenConeMap_toAmbient f g a b h)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph g).ker ≫ k)
          (OpenAmbient.BundleCycles.graphOpenAmbientMap_first f g a b)).trans (Category.assoc _ _ _).symm)))

theorem graphOpenConeMap_over :
    graphOpenConeMap f g a b h ≫ Chow.BundleCycles.graphConeStructureMap f = Chow.BundleCycles.graphConeStructureMap g := by
  exact (congrArg (fun k => graphOpenConeMap f g a b h ≫ k) (Chow.BundleCycles.graphConeStructureMap_normal f)).symm.trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ X.structureMap) (graphOpenConeMap_normal f g a b h)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => Chow.BundleCycles.graphNormalProjection g ≫ k) a.w).trans (Chow.BundleCycles.graphConeStructureMap_normal g)))))

theorem graphNormalPointPullback_open (z : X.carrier →₀ ℚ) :
    Finsupp.comapDomain (graphOpenConeMap f g a b h) (Chow.BundleCycles.graphNormalPointPullback f z)
      (graphOpenConeMap f g a b h).isOpenEmbedding.injective.injOn =
      Chow.BundleCycles.graphNormalPointPullback g (Finsupp.comapDomain a.left z a.left.isOpenEmbedding.injective.injOn) :=
  @Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_openSquare _ X.carrier _ X'.carrier
    (Chow.BundleCycles.graphNormalProjection f) (Chow.BundleCycles.graphNormalProjection g) inferInstance inferInstance
    a.left (graphOpenConeMap f g a b h) (inferInstanceAs (IsOpenImmersion a.left))
    (graphOpenConeMap_open f g a b h) (graphOpenConeMap_normal f g a b h).symm z

theorem graphCycleSpecialization_open (z : OpenAmbient.BundleCycles.graphAmbient f →₀ ℚ) :
    Finsupp.comapDomain (graphOpenConeMap f g a b h) (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker z)
      (graphOpenConeMap f g a b h).isOpenEmbedding.injective.injOn =
      Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph g).ker
        (Finsupp.comapDomain (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b) z
          (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b).isOpenEmbedding.injective.injOn) :=
  Open.SpecialFiberIdentifiedIdeal.BundleCycles.globalCycleSpecialization_open_identified (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b) (OpenAmbient.BundleCycles.graph f).ker (OpenAmbient.BundleCycles.graph g).ker
    (OpenSquare.BundleCycles.graphOpenAmbientMap_kernel f g a b h) z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenCone.BundleCycles
