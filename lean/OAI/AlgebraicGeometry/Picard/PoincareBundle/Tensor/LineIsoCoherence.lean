import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrMapComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

/-! # Line Iso Coherence -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineIsoCoherence

noncomputable section

/-! Naturality and composition of the actual line-bundle tensor pullback isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrMapComparison

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

theorem naturality {M M' N N' : Y.Modules}
    (hM : Line.Bundles.IsLine M) (hM' : Line.Bundles.IsLine M')
    (hN : Line.Bundles.IsLine N) (hN' : Line.Bundles.IsLine N') (a : M ≅ M') (b : N ≅ N') :
    (Scheme.Modules.pullback f).mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) ≪≫ LinePullback.pullbackIso f M' N' hM' hN' =
      LinePullback.pullbackIso f M N hM hN ≪≫
        AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ((Scheme.Modules.pullback f).mapIso a) ((Scheme.Modules.pullback f).mapIso b) := by
  apply Iso.ext
  change (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b).hom ≫ PullbackMap.pullbackMap f M' N' =
    PullbackMap.pullbackMap f M N ≫ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ((Scheme.Modules.pullback f).mapIso a)
      ((Scheme.Modules.pullback f).mapIso b)).hom
  rw [CongrMapComparison.congr_hom, CongrMapComparison.congr_hom]
  exact PullbackMap.pullbackMap_naturality f a.hom b.hom

theorem composition (g : Y ⟶ Z) (M N : Z.Modules)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N) :
    LinePullback.pullbackIso (f ≫ g) M N hM hN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
      ((Scheme.Modules.pullbackComp f g).app M).symm ((Scheme.Modules.pullbackComp f g).app N).symm =
    ((Scheme.Modules.pullbackComp f g).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)).symm ≪≫
      (Scheme.Modules.pullback f).mapIso (LinePullback.pullbackIso g M N hM hN) ≪≫
        LinePullback.pullbackIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
          (hM.pullback g) (hN.pullback g) := by
  apply Iso.ext
  change PullbackMap.pullbackMap (f ≫ g) M N ≫ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
      ((Scheme.Modules.pullbackComp f g).app M).symm ((Scheme.Modules.pullbackComp f g).app N).symm).hom =
    (Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≫
      (Scheme.Modules.pullback f).map (PullbackMap.pullbackMap g M N) ≫
        PullbackMap.pullbackMap f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
  rw [CongrMapComparison.congr_hom]
  exact PullbackComposition.pullbackMap_comp_inv f g M N

theorem congr_map {f' : X ⟶ Y} (h : f = f') (M N : Y.Modules)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N) :
    (Scheme.Modules.pullbackCongr h).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫ LinePullback.pullbackIso f' M N hM hN =
      LinePullback.pullbackIso f M N hM hN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
        ((Scheme.Modules.pullbackCongr h).app M) ((Scheme.Modules.pullbackCongr h).app N) := by
  subst f'
  apply Iso.ext
  change (𝟙 _) ≫ PullbackMap.pullbackMap f M N = PullbackMap.pullbackMap f M N ≫
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) (Iso.refl _)).hom
  rw [CongrMapComparison.congr_hom]
  simp only [Iso.refl_hom, SheafMaps.tensorMap_id, Category.id_comp, Category.comp_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineIsoCoherence
