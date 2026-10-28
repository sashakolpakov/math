import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.TensorCompositionUnits

/-! # Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.PullbackComposition

noncomputable section

/-! Composition of the bilinear maps induced by the units of pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem bilinearPullbackUnit_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules)
    (P : X.Modules) (β : Sheaves.SheafBilinearMap ((Scheme.Modules.pullback (f ≫ g)).obj M)
      ((Scheme.Modules.pullback (f ≫ g)).obj N) P) :
    (Tensor.PullbackComparison.bilinearPullbackUnit g M N ((Scheme.Modules.pushforward f).obj P)
      (Tensor.PullbackComparison.bilinearPullbackUnit f ((Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback g).obj N) P
        (β.precomp ((Scheme.Modules.pullbackComp f g).hom.app M)
          ((Scheme.Modules.pullbackComp f g).hom.app N)))).postcomp
      ((Scheme.Modules.pushforwardComp f g).hom.app P) =
      Tensor.PullbackComparison.bilinearPullbackUnit (f ≫ g) M N P β := by
  unfold Tensor.PullbackComparison.bilinearPullbackUnit
  rw [Sheaves.SheafBilinearMap.pushforward_precomp, Sheaves.SheafBilinearMap.pushforward_precomp,
    Sheaves.SheafBilinearMap.pushforward_precomp, Sheaves.SheafBilinearMap.precomp_comp,
    Sheaves.SheafBilinearMap.precomp_comp, ← Sheaves.SheafBilinearMap.precomp_postcomp,
    Sheaves.SheafBilinearMap.pushforward_comp, Sheaves.SheafBilinearMap.precomp_comp]
  apply congrArg₂ (fun a b => (β.pushforward (f ≫ g)).precomp a b)
  · simpa only [Functor.map_comp, Category.assoc] using Pullback.TensorCompositionUnits.pullbackComp_hom_unit f g M
  · simpa only [Functor.map_comp, Category.assoc] using Pullback.TensorCompositionUnits.pullbackComp_hom_unit f g N

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.PullbackComposition
