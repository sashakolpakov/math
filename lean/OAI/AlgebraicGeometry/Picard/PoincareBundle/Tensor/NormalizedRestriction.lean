import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FixedRestriction

/-! # Normalized Restriction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.NormalizedRestriction

noncomputable section

/-! Tensor products of normalized line symmetries retain the actual restriction normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FixedRestriction

theorem normalized_tensor {X Y : Scheme.{u}} (p : X ⟶ Y) (g : Y ⟶ Y) (h : p ≫ g = p)
    (M N : Y.Modules) (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
    (a : (Scheme.Modules.pullback g).obj M ≅ M) (b : (Scheme.Modules.pullback g).obj N ≅ N)
    (ha : (Scheme.Modules.pullback p).mapIso a = FixedRestriction.comparison p g h M)
    (hb : (Scheme.Modules.pullback p).mapIso b = FixedRestriction.comparison p g h N) :
    (Scheme.Modules.pullback p).mapIso (LinePullback.pullbackIso g M N hM hN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) =
      FixedRestriction.comparison p g h (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) := by
  let D := (Scheme.Modules.pullback p).mapIso (LinePullback.pullbackIso g M N hM hN)
  let R := LinePullback.pullbackIso p M N hM hN
  let R' := LinePullback.pullbackIso p ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
    (hM.pullback g) (hN.pullback g)
  have hn := LineIsoCoherence.naturality p (hM.pullback g) hM (hN.pullback g) hN a b
  have hn' : (Scheme.Modules.pullback p).mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) ≪≫ R =
      R' ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (FixedRestriction.comparison p g h M) (FixedRestriction.comparison p g h N) :=
    hn.trans (congrArg (fun q => R' ≪≫ q) (congrArg₂ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ha hb))
  have he : (Scheme.Modules.pullback p).mapIso (LinePullback.pullbackIso g M N hM hN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) ≪≫ R =
      FixedRestriction.comparison p g h (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫ R := by
    calc
      (Scheme.Modules.pullback p).mapIso (LinePullback.pullbackIso g M N hM hN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) ≪≫ R =
          D ≪≫ ((Scheme.Modules.pullback p).mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) ≪≫ R) := by
        rw [Functor.mapIso_trans, Iso.trans_assoc]
      _ = D ≪≫ (R' ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (FixedRestriction.comparison p g h M) (FixedRestriction.comparison p g h N)) :=
        congrArg (fun q => D ≪≫ q) hn'
      _ = FixedRestriction.comparison p g h (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫ R := FixedRestriction.tensor_comparison p g h M N hM hN
  apply Iso.ext
  apply (cancel_mono R.hom).mp
  exact congrArg Iso.hom he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.NormalizedRestriction
