import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.PullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackOpen

/-! # Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackComposition

noncomputable section

/-! The canonical tensor-pullback comparison commutes with composition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem tensorPullbackComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    (Scheme.Modules.pullback f).map (PullbackComparison.tensorPullbackComparison g M N) ≫
      PullbackComparison.tensorPullbackComparison f ((Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback g).obj N) ≫
      Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app M)
        ((Scheme.Modules.pullbackComp f g).hom.app N) =
      (Scheme.Modules.pullbackComp f g).hom.app (ProductSheaf.tensorModule M N) ≫
        PullbackComparison.tensorPullbackComparison (f ≫ g) M N := by
  let P := ProductSheaf.tensorModule ((Scheme.Modules.pullback (f ≫ g)).obj M)
    ((Scheme.Modules.pullback (f ≫ g)).obj N)
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ P).injective
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _
    ((Scheme.Modules.pushforward f).obj P)).injective
  apply (cancel_mono ((Scheme.Modules.pushforwardComp f g).hom.app P)).mp
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [Pullback.TensorCompositionUnits.pullbackComp_homEquiv, PullbackComparison.tensorPullbackComparison_spec,
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left]
  let a := Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app M)
    ((Scheme.Modules.pullbackComp f g).hom.app N)
  have hf := PullbackOpen.tensorPullbackComparison_homEquiv f ((Scheme.Modules.pullback g).obj M)
    ((Scheme.Modules.pullback g).obj N) P a
  have hg := PullbackOpen.tensorPullbackComparison_homEquiv g M N ((Scheme.Modules.pushforward f).obj P)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ P
      (PullbackComparison.tensorPullbackComparison f ((Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback g).obj N) ≫ a))
  have ha : Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ P a =
      (Bifunctor.tensorBilinear ((Scheme.Modules.pullback (f ≫ g)).obj M)
        ((Scheme.Modules.pullback (f ≫ g)).obj N)).precomp
        ((Scheme.Modules.pullbackComp f g).hom.app M)
        ((Scheme.Modules.pullbackComp f g).hom.app N) :=
    (Bifunctor.tensorBilinear_postcomp a).symm.trans (Bifunctor.tensorModuleMap_spec _ _)
  exact (congrArg (fun β => β.postcomp ((Scheme.Modules.pushforwardComp f g).hom.app P)) hg).trans
    ((congrArg (fun β => (PullbackComparison.bilinearPullbackUnit g M N ((Scheme.Modules.pushforward f).obj P) β).postcomp
      ((Scheme.Modules.pushforwardComp f g).hom.app P)) hf).trans
      ((congrArg (fun β => (PullbackComparison.bilinearPullbackUnit g M N ((Scheme.Modules.pushforward f).obj P)
        (PullbackComparison.bilinearPullbackUnit f ((Scheme.Modules.pullback g).obj M)
          ((Scheme.Modules.pullback g).obj N) P β)).postcomp
            ((Scheme.Modules.pushforwardComp f g).hom.app P)) ha).trans
        (Bilinear.PullbackComposition.bilinearPullbackUnit_comp f g M N P _)))

theorem tensorPullbackComparison_isIso_of_trivial {M N : Y.Modules} (f : X ⟶ Y)
    (e : M ≅ Line.Bundles.structureModule Y) (d : N ≅ Line.Bundles.structureModule Y)
    [IsIso (PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule Y) (Line.Bundles.structureModule Y))] :
    IsIso (PullbackComparison.tensorPullbackComparison f M N) := by
  have h : IsIso (PullbackComparison.tensorPullbackComparison f M N ≫
      Bifunctor.tensorModuleMap ((Scheme.Modules.pullback f).map e.hom)
        ((Scheme.Modules.pullback f).map d.hom)) := by
    rw [← PullbackComparison.tensorPullbackComparison_natural]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackComposition
