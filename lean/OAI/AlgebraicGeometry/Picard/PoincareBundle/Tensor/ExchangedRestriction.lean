import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FixedRestriction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackSwap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SwapNaturality

/-! # Exchanged Restriction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ExchangedRestriction

noncomputable section

/-! Exchanged line factors give a normalized tensor symmetry when their restricted identifications agree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FixedRestriction

theorem normalized_exchange {X Y : Scheme.{u}} (p : X ⟶ Y) (g : Y ⟶ Y) (h : p ≫ g = p)
    (M N : Y.Modules) (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
    (a : (Scheme.Modules.pullback g).obj M ≅ N) (b : (Scheme.Modules.pullback g).obj N ≅ M)
    (e : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj N)
    (ha : (Scheme.Modules.pullback p).mapIso a = FixedRestriction.comparison p g h M ≪≫ e)
    (hb : (Scheme.Modules.pullback p).mapIso b = FixedRestriction.comparison p g h N ≪≫ e.symm) :
    (Scheme.Modules.pullback p).mapIso
      (LinePullback.pullbackIso g M N hM hN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N M) =
      FixedRestriction.comparison p g h (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) := by
  let F := Scheme.Modules.pullback p
  let D := F.mapIso (LinePullback.pullbackIso g M N hM hN)
  let R := LinePullback.pullbackIso p M N hM hN
  let R' := LinePullback.pullbackIso p ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
    (hM.pullback g) (hN.pullback g)
  let K := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (FixedRestriction.comparison p g h M) (FixedRestriction.comparison p g h N)
  let C := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (F.obj N) (F.obj M)
  have hlast : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (F.mapIso a) (F.mapIso b) ≪≫ C = K := by
    calc
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (F.mapIso a) (F.mapIso b) ≪≫ C =
          AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (FixedRestriction.comparison p g h M ≪≫ e) (FixedRestriction.comparison p g h N ≪≫ e.symm) ≪≫ C :=
        congrArg (fun q => q ≪≫ C) (congrArg₂ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ha hb)
      _ = K ≪≫ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr e e.symm ≪≫ C) := by
        rw [← CongrComposition.trans, Iso.trans_assoc]
      _ = K := by
        rw [SwapNaturality.identified_swap (show ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle (F.obj M) from hM.pullback p) e,
          Iso.trans_refl]
  have hn := LineIsoCoherence.naturality p (hM.pullback g) hN (hN.pullback g) hM a b
  have hs := PullbackSwap.iso_swap p N M hN hM
  have he : F.mapIso
      (LinePullback.pullbackIso g M N hM hN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N M) ≪≫ R =
      FixedRestriction.comparison p g h (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫ R := by
    calc
      F.mapIso (LinePullback.pullbackIso g M N hM hN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N M) ≪≫ R =
          D ≪≫ F.mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) ≪≫ (F.mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N M) ≪≫ R) := by
        rw [Functor.mapIso_trans, Functor.mapIso_trans]
        simp only [D, Iso.trans_assoc]
      _ = D ≪≫ F.mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) ≪≫ (LinePullback.pullbackIso p N M hN hM ≪≫ C) :=
        congrArg (fun q => D ≪≫ F.mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) ≪≫ q) hs
      _ = D ≪≫ (R' ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (F.mapIso a) (F.mapIso b)) ≪≫ C := by
        rw [← Iso.trans_assoc (F.mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b)), hn]
      _ = D ≪≫ R' ≪≫ K := by rw [Iso.trans_assoc, hlast]
      _ = FixedRestriction.comparison p g h (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫ R := FixedRestriction.tensor_comparison p g h M N hM hN
  apply Iso.ext
  apply (cancel_mono R.hom).mp
  exact congrArg Iso.hom he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ExchangedRestriction
