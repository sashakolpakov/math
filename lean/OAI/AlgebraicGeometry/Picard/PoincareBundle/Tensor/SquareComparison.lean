import OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedLineEquivariance
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CompositionForward

/-! # Square Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SquareComparison

noncomputable section

/-! The canonical comparison of an invariant square respects tensor products of actual lines. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedLineEquivariance

variable {S : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y) (g : Y ⟶ Y) (b : X ⟶ X)
  (h : b ≫ p = p ≫ g) (M N : Y.left.Modules)
  (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)

theorem tensor_comparison :
    (Scheme.Modules.pullback b.left).mapIso (LinePullback.pullbackIso p.left M N hM hN) ≪≫
      LinePullback.pullbackIso b.left ((Scheme.Modules.pullback p.left).obj M) ((Scheme.Modules.pullback p.left).obj N)
        (hM.pullback p.left) (hN.pullback p.left) ≪≫
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ((RestrictedLineEquivariance.comparison p g b h).app M) ((RestrictedLineEquivariance.comparison p g b h).app N) =
    (RestrictedLineEquivariance.comparison p g b h).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫
      (Scheme.Modules.pullback p.left).mapIso (LinePullback.pullbackIso g.left M N hM hN) ≪≫
      LinePullback.pullbackIso p.left ((Scheme.Modules.pullback g.left).obj M) ((Scheme.Modules.pullback g.left).obj N)
        (hM.pullback g.left) (hN.pullback g.left) := by
  let CM := (Scheme.Modules.pullbackComp b.left p.left).app M
  let CN := (Scheme.Modules.pullbackComp b.left p.left).app N
  let CT := (Scheme.Modules.pullbackComp b.left p.left).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)
  let EM := (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app M
  let EN := (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app N
  let ET := (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)
  let DM := (Scheme.Modules.pullbackComp p.left g.left).app M
  let DN := (Scheme.Modules.pullbackComp p.left g.left).app N
  let DT := (Scheme.Modules.pullbackComp p.left g.left).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)
  let U := (Scheme.Modules.pullback b.left).mapIso (LinePullback.pullbackIso p.left M N hM hN) ≪≫
    LinePullback.pullbackIso b.left ((Scheme.Modules.pullback p.left).obj M) ((Scheme.Modules.pullback p.left).obj N)
      (hM.pullback p.left) (hN.pullback p.left)
  let V := (Scheme.Modules.pullback p.left).mapIso (LinePullback.pullbackIso g.left M N hM hN) ≪≫
    LinePullback.pullbackIso p.left ((Scheme.Modules.pullback g.left).obj M) ((Scheme.Modules.pullback g.left).obj N)
      (hM.pullback g.left) (hN.pullback g.left)
  let R := LinePullback.pullbackIso (b.left ≫ p.left) M N hM hN
  let R' := LinePullback.pullbackIso (p.left ≫ g.left) M N hM hN
  have hU : U ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr CM CN = CT ≪≫ R :=
    (Iso.trans_assoc _ _ _).trans (CompositionForward.composition b.left p.left M N hM hN)
  have hR : ET ≪≫ R' = R ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr EM EN :=
    LineIsoCoherence.congr_map (b.left ≫ p.left) (congrArg Over.Hom.left h) M N hM hN
  have hV : R' ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr DM.symm DN.symm = DT.symm ≪≫ V :=
    LineIsoCoherence.composition p.left g.left M N hM hN
  have ht : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ((RestrictedLineEquivariance.comparison p g b h).app M) ((RestrictedLineEquivariance.comparison p g b h).app N) =
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr CM CN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr EM EN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr DM.symm DN.symm := by
    change AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (CM ≪≫ EM ≪≫ DM.symm) (CN ≪≫ EN ≪≫ DN.symm) = _
    rw [CongrComposition.trans, CongrComposition.trans]
  change _ = (CT ≪≫ ET ≪≫ DT.symm) ≪≫ V
  calc
    _ = U ≪≫ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr CM CN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr EM EN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr DM.symm DN.symm) :=
      (Iso.trans_assoc _ _ _).symm.trans (congrArg (fun e => U ≪≫ e) ht)
    _ = CT ≪≫ (R ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr EM EN) ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr DM.symm DN.symm := by
      rw [← Iso.trans_assoc, hU, Iso.trans_assoc, ← Iso.trans_assoc R]
    _ = CT ≪≫ (ET ≪≫ R') ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr DM.symm DN.symm :=
      congrArg (fun e => CT ≪≫ e ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr DM.symm DN.symm) hR.symm
    _ = CT ≪≫ ET ≪≫ DT.symm ≪≫ V := by rw [Iso.trans_assoc, hV]
    _ = (CT ≪≫ ET ≪≫ DT.symm) ≪≫ V := by simp only [Iso.trans_assoc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SquareComparison
