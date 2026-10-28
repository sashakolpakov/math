import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SquareComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles

/-! # Restricted Tensor Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedTensorSymmetry

noncomputable section

/-! Restricting a tensor symmetry is compatible with the actual tensor pullback isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedLineEquivariance

variable {S : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y) (g : Y ⟶ Y) (b : X ⟶ X)
  (h : b ≫ p = p ≫ g) (M N : Line.Bundles.LineBundle Y.left)
  (a : (Scheme.Modules.pullback g.left).obj M.sheaf ≅ M.sheaf)
  (d : (Scheme.Modules.pullback g.left).obj N.sheaf ≅ N.sheaf)

theorem tensor_symmetry :
    (Scheme.Modules.pullback b.left).mapIso (Tensor.LinePullback.pullbackIso p.left M.sheaf N.sheaf M.isLine N.isLine) ≪≫
      Tensor.LinePullback.pullbackIso b.left ((Scheme.Modules.pullback p.left).obj M.sheaf) ((Scheme.Modules.pullback p.left).obj N.sheaf)
        (M.isLine.pullback p.left) (N.isLine.pullback p.left) ≪≫
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (RestrictedLineEquivariance.symmetry p g b h M a) (RestrictedLineEquivariance.symmetry p g b h N d) =
    RestrictedLineEquivariance.symmetry p g b h (Tensor.LineBundles.tensor M N)
      (Tensor.LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a d) ≪≫
      Tensor.LinePullback.pullbackIso p.left M.sheaf N.sheaf M.isLine N.isLine := by
  let U := (Scheme.Modules.pullback b.left).mapIso (Tensor.LinePullback.pullbackIso p.left M.sheaf N.sheaf M.isLine N.isLine)
  let V := Tensor.LinePullback.pullbackIso b.left ((Scheme.Modules.pullback p.left).obj M.sheaf) ((Scheme.Modules.pullback p.left).obj N.sheaf)
    (M.isLine.pullback p.left) (N.isLine.pullback p.left)
  let CM := (RestrictedLineEquivariance.comparison p g b h).app M.sheaf
  let CN := (RestrictedLineEquivariance.comparison p g b h).app N.sheaf
  let CT := (RestrictedLineEquivariance.comparison p g b h).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf N.sheaf)
  let D := (Scheme.Modules.pullback p.left).mapIso (Tensor.LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine)
  let R := Tensor.LinePullback.pullbackIso p.left ((Scheme.Modules.pullback g.left).obj M.sheaf) ((Scheme.Modules.pullback g.left).obj N.sheaf)
    (M.isLine.pullback g.left) (N.isLine.pullback g.left)
  let a' := (Scheme.Modules.pullback p.left).mapIso a
  let d' := (Scheme.Modules.pullback p.left).mapIso d
  have hc : U ≪≫ V ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr CM CN = CT ≪≫ D ≪≫ R :=
    Tensor.SquareComparison.tensor_comparison p g b h M.sheaf N.sheaf M.isLine N.isLine
  have hn : (Scheme.Modules.pullback p.left).mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a d) ≪≫
      Tensor.LinePullback.pullbackIso p.left M.sheaf N.sheaf M.isLine N.isLine = R ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a' d' :=
    Tensor.LineIsoCoherence.naturality p.left (M.isLine.pullback g.left) M.isLine
      (N.isLine.pullback g.left) N.isLine a d
  rw [RestrictedLineEquivariance.symmetry_eq, RestrictedLineEquivariance.symmetry_eq, RestrictedLineEquivariance.symmetry_eq]
  dsimp only [Line.Fibers.fiber, Functor.comp_obj, Tensor.LineBundles.tensor]
  rw [Functor.mapIso_trans]
  change U ≪≫ V ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (CM ≪≫ a') (CN ≪≫ d') =
    (CT ≪≫ D ≪≫ (Scheme.Modules.pullback p.left).mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a d)) ≪≫
      Tensor.LinePullback.pullbackIso p.left M.sheaf N.sheaf M.isLine N.isLine
  rw [← Tensor.CongrComposition.trans, ← Iso.trans_assoc V, ← Iso.trans_assoc U, hc]
  rw [Iso.trans_assoc, Iso.trans_assoc, ← hn]
  simp only [Iso.trans_assoc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedTensorSymmetry
