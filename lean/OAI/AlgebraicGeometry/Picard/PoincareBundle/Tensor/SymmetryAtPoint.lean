import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineIsoCoherence
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFibers

/-! # Symmetry At Point -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SymmetryAtPoint

noncomputable section

/-! Evaluation of a tensor symmetry is the tensor of the two actual fiber symmetries. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

theorem three_squares {C : Type*} [Category C] {A B D E F G : C}
    (p : A ≅ B) (z : B ≅ D) (r : D ≅ E) (w : B ≅ F) (v : F ≅ E)
    (r' : A ≅ G) (u : G ≅ F) (s : A ≅ D) (t : G ≅ E)
    (hs : s = p ≪≫ z) (hn : z ≪≫ r = w ≪≫ v) (hc : r' ≪≫ u = p ≪≫ w) (ht : t = u ≪≫ v) :
    s ≪≫ r = r' ≪≫ t := by
  rw [hs, Iso.trans_assoc, hn, ← Iso.trans_assoc, ← hc, Iso.trans_assoc, ← ht]

variable {S : Scheme.{u}} {E : Over S} (M N : Line.Bundles.LineBundle E.left) (g : E ⟶ E)
  (a : (Scheme.Modules.pullback g.left).obj M.sheaf ≅ M.sheaf)
  (b : (Scheme.Modules.pullback g.left).obj N.sheaf ≅ N.sheaf)

/-- Canonical tensor pullback comparisons identify the evaluated tensor symmetry with the tensor
of the individually evaluated symmetries, on every test scheme. -/
theorem atPoint {T : Over S} (q : T ⟶ E) :
    Line.SymmetryFibers.atPoint (LineBundles.tensor M N) g
        (LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) q ≪≫
      LinePullback.pullbackIso q.left M.sheaf N.sheaf M.isLine N.isLine =
    LinePullback.pullbackIso (q ≫ g).left M.sheaf N.sheaf M.isLine N.isLine ≪≫
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Line.SymmetryFibers.atPoint M g a q) (Line.SymmetryFibers.atPoint N g b q) := by
  let cm := (Scheme.Modules.pullbackComp q.left g.left).app M.sheaf
  let cn := (Scheme.Modules.pullbackComp q.left g.left).app N.sheaf
  let ct := (Scheme.Modules.pullbackComp q.left g.left).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf N.sheaf)
  let d := (Scheme.Modules.pullback q.left).mapIso (LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine)
  let z := (Scheme.Modules.pullback q.left).mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b)
  let w := LinePullback.pullbackIso q.left ((Scheme.Modules.pullback g.left).obj M.sheaf)
    ((Scheme.Modules.pullback g.left).obj N.sheaf) (M.isLine.pullback g.left) (N.isLine.pullback g.left)
  let r := LinePullback.pullbackIso q.left M.sheaf N.sheaf M.isLine N.isLine
  let r' := LinePullback.pullbackIso (q ≫ g).left M.sheaf N.sheaf M.isLine N.isLine
  let u := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr cm.symm cn.symm
  let v := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ((Scheme.Modules.pullback q.left).mapIso a) ((Scheme.Modules.pullback q.left).mapIso b)
  let s := Line.SymmetryFibers.atPoint (LineBundles.tensor M N) g
    (LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) q
  let t := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Line.SymmetryFibers.atPoint M g a q) (Line.SymmetryFibers.atPoint N g b q)
  have hs : s = (ct.symm ≪≫ d) ≪≫ z :=
    (Line.SymmetryFibers.atPoint_eq (LineBundles.tensor M N) g
      (LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) q).trans
      ((congrArg (fun e => ct.symm ≪≫ e) (Functor.mapIso_trans (Scheme.Modules.pullback q.left)
        (LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine) (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b))).trans
        (Iso.trans_assoc _ _ _).symm)
  have hn : z ≪≫ r = w ≪≫ v :=
    LineIsoCoherence.naturality q.left (M.isLine.pullback g.left) M.isLine
      (N.isLine.pullback g.left) N.isLine a b
  have hc : r' ≪≫ u = (ct.symm ≪≫ d) ≪≫ w :=
    (LineIsoCoherence.composition q.left g.left M.sheaf N.sheaf M.isLine N.isLine).trans
      (Iso.trans_assoc _ _ _).symm
  have ht : t = u ≪≫ v :=
    (congrArg₂ (fun x y => AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr x y)
      (Line.SymmetryFibers.atPoint_eq M g a q) (Line.SymmetryFibers.atPoint_eq N g b q)).trans
      (CongrComposition.trans cm.symm cn.symm ((Scheme.Modules.pullback q.left).mapIso a)
        ((Scheme.Modules.pullback q.left).mapIso b)).symm
  exact three_squares (ct.symm ≪≫ d) z r w v r' u s t hs hn hc ht

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SymmetryAtPoint
