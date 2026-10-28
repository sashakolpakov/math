import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Pullback From Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.PullbackFromCharts

noncomputable section

/-! Compatible Cartesian charts identify a global square as a pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem scheme_isPullback_of_cartesian_charts
    {W Y S T : Scheme.{u}} (q : W ⟶ Y) (p : W ⟶ S) (f : Y ⟶ T) (b : S ⟶ T)
    (U : Y.OpenCover) (P : U.I₀ → Scheme.{u})
    (qi : ∀ i, P i ⟶ U.X i) (ai : ∀ i, P i ⟶ W)
    (hchart : ∀ i, IsPullback (qi i) (ai i) (U.f i) q)
    (hbase : ∀ i, IsPullback (qi i) (ai i ≫ p) (U.f i ≫ f) b) :
    IsPullback q p f b := by
  apply Scheme.isPullback_of_openCover q p f b U
  intro i
  change IsPullback (pullback.snd q (U.f i)) (pullback.fst q (U.f i) ≫ p) (U.f i ≫ f) b
  apply (hbase i).of_iso (hchart i).flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using (hchart i).flip.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc, (hchart i).flip.isoPullback_hom_fst]
  · simp
  · simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.PullbackFromCharts
