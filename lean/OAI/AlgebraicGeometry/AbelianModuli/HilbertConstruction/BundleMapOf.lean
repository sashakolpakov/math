import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.BundleMapComposition
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Bundle Map Of -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundleMapOf

noncomputable section

/-! The overlap condition for maps between pullbacks of line bundles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def BundleMapDescentCondition (f : Y ⟶ X) {L M : Line.Bundles.LineBundle X}
    (φ : (L.pullback f).sheaf ⟶ (M.pullback f).sheaf) : Prop :=
  CommSq (Pullback.BundleMapComposition.pullbackBundleMapComp (pullback.fst f f) f φ)
    ((Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := f))).hom.app L.sheaf)
    ((Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := f))).hom.app M.sheaf)
    (Pullback.BundleMapComposition.pullbackBundleMapComp (pullback.snd f f) f φ)

theorem bundleMapDescentCondition_of_pullback (f : Y ⟶ X) {L M : Line.Bundles.LineBundle X}
    (φ : L.sheaf ⟶ M.sheaf) : BundleMapDescentCondition f ((Scheme.Modules.pullback f).map φ) := by
  unfold BundleMapDescentCondition
  rw [Pullback.BundleMapComposition.pullbackBundleMapComp_of_pullback, Pullback.BundleMapComposition.pullbackBundleMapComp_of_pullback]
  exact ⟨(Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := f))).hom.naturality φ⟩

theorem BundleMapDescentCondition.comp (f : Y ⟶ X) {L M N : Line.Bundles.LineBundle X}
    {φ : (L.pullback f).sheaf ⟶ (M.pullback f).sheaf}
    {ψ : (M.pullback f).sheaf ⟶ (N.pullback f).sheaf}
    (hφ : BundleMapDescentCondition f φ) (hψ : BundleMapDescentCondition f ψ) :
    BundleMapDescentCondition f (φ ≫ ψ) := by
  unfold BundleMapDescentCondition at hφ hψ ⊢
  rw [Pullback.BundleMapComposition.pullbackBundleMapComp_comp, Pullback.BundleMapComposition.pullbackBundleMapComp_comp]
  exact hφ.horiz_comp hψ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundleMapOf
