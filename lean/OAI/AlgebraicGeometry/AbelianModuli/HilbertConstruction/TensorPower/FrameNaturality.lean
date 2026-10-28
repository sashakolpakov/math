import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.ProductPullbacks

/-! # Frame Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.FrameNaturality

noncomputable section

/-! The frame-independent tensor-power comparison commutes with module isomorphisms and open pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem tensorPowerFrameComparisonIso_natural {L L' M M' : X.Modules}
    (e : Line.Bundles.structureModule X ⟶ L) (t : Line.Bundles.structureModule X ⟶ M) [IsIso e] [IsIso t]
    (a : L ⟶ L') (b : M ⟶ M') [IsIso a] [IsIso b] (n : ℕ) :
    Maps.tensorPowerMap (Tensor.Bifunctor.tensorModuleMap a b) n ≫ (FrameComparison.tensorPowerFrameComparisonIso (e ≫ a) (t ≫ b) n).hom =
      (FrameComparison.tensorPowerFrameComparisonIso e t n).hom ≫ Tensor.Bifunctor.tensorModuleMap (Maps.tensorPowerMap a n) (Maps.tensorPowerMap b n) := by
  apply (cancel_epi (Maps.tensorPowerSection (Tensor.ProductSections.tensorProductSection e t) n)).mp
  rw [← Category.assoc, ProductPullbacks.tensorPowerSection_postcomp, Tensor.ProductSections.tensorProductSection_postcomp,
    FrameComparison.tensorPowerFrameComparisonIso_frame, ← Category.assoc, FrameComparison.tensorPowerFrameComparisonIso_frame,
    Tensor.ProductSections.tensorProductSection_postcomp, ProductPullbacks.tensorPowerSection_postcomp, ProductPullbacks.tensorPowerSection_postcomp]

theorem tensorPowerFrameComparisonIso_pullback (f : X ⟶ Y) [IsOpenImmersion f]
    {L M : Y.Modules} (e : Line.Bundles.structureModule Y ⟶ L) (t : Line.Bundles.structureModule Y ⟶ M)
    [IsIso e] [IsIso t] (n : ℕ) :
    (Scheme.Modules.pullback f).map (FrameComparison.tensorPowerFrameComparisonIso e t n).hom ≫
      (ProductPullbacks.tensorOfPowersPullbackIso f L M n).hom =
      (ProductPullbacks.tensorPowerOfTensorPullbackIso f L M n).hom ≫
        (FrameComparison.tensorPowerFrameComparisonIso (Ample.LineBundles.pullbackSection f e) (Ample.LineBundles.pullbackSection f t) n).hom := by
  apply (cancel_epi (Ample.LineBundles.pullbackSection f (Maps.tensorPowerSection (Tensor.ProductSections.tensorProductSection e t) n))).mp
  rw [← Category.assoc, ← Power.SectionTransitions.pullbackSection_postcomp, FrameComparison.tensorPowerFrameComparisonIso_frame,
    ProductPullbacks.tensorOfPowersPullbackIso_section, ← Category.assoc, ProductPullbacks.tensorPowerOfTensorPullbackIso_section,
    FrameComparison.tensorPowerFrameComparisonIso_frame]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.FrameNaturality
