import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PicardSquareComparison

/-! # Iso Poincare Local -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoPoincareLocal

noncomputable section

/-! Recovery of the native abelian and dual maps gives the original
Poincare equality after the actual simultaneous base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

theorem levelIso_poincare_after_pullback {S Y : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (u : Y ⟶ S)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback u) (B.pullback u))
    (a : A.abelian.scheme ⟶ B.abelian.scheme) (d : A.dual.abelian.scheme ⟶ B.dual.abelian.scheme)
    (ha : (Over.pullback u).map a = e.abelian.hom) (hd : (Over.pullback u).map d = e.dual.hom) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.dual.poincarePullbackOverMap u).left
      (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ a).left (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)) =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.dual.poincarePullbackOverMap u).left (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) := by
  have hp : ((Over.pullback u).map d ⊗ₘ (Over.pullback u).map a).left =
      (e.dual.hom ⊗ₘ e.abelian.hom).left := congrArg₂
    (fun (x : (Over.pullback u).obj A.dual.abelian.scheme ⟶ (Over.pullback u).obj B.dual.abelian.scheme)
      (y : (Over.pullback u).obj A.abelian.scheme ⟶ (Over.pullback u).obj B.abelian.scheme) => (x ⊗ₘ y).left) hd ha
  exact (PicardSquareComparison.picardPullback_square _ _ _ _ (HilbertConstruction.Moduli.BaseChange.poincarePullbackOverMap_naturality A.dual B.dual d a u)
    (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)).symm.trans
      ((congrArg (fun f => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f
        (HilbertConstruction.Line.Bundles.LineBundle.classOf (B.pullback u).dual.poincare)) hp).trans e.poincare)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoPoincareLocal
