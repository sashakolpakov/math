import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareClassCoverDetection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareProductZero
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoPoincareLocal

/-! # Iso Poincare Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoPoincareDescent

noncomputable section

/-! The native Poincare equation descends from the recovered local
group maps, with actual normalization and effective line descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem levelIso_poincare_descends {S Y : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (u : Y ⟶ S)
    [Flat u] [Surjective u] [QuasiCompact u]
    (hΓ : ∀ V : Over S, IsIso (fst V A.abelian.scheme).left.appTop)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback u) (B.pullback u))
    (a : A.abelian.scheme ⟶ B.abelian.scheme) (d : A.dual.abelian.scheme ⟶ B.dual.abelian.scheme)
    [IsMonHom a] (ha : (Over.pullback u).map a = e.abelian.hom) (hd : (Over.pullback u).map d = e.dual.hom) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ a).left (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare :=
  PoincareClassCoverDetection.poincareClass_eq_of_baseChange A.dual u hΓ (HilbertConstruction.Line.Bundles.LineBundle.pullback (d ⊗ₘ a).left B.dual.poincare) A.dual.poincare
    (PoincareProductZero.poincareProduct_zeroIso A.dual B.dual a d) A.dual.normalizedAtAbelianZero.some
    (IsoPoincareLocal.levelIso_poincare_after_pullback A B u e a d ha hd)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoPoincareDescent
