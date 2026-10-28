import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus

/-! # Cartesian Morphism Isomorphism Comparison -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CartesianMorphismIsomorphismComparison

noncomputable section

/-! An actual morphism between two Cartesian family presentations is
an isomorphism exactly when the canonical base-changed morphism is. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B T X' Y' : Scheme.{u}}

theorem relativeMorphismBaseChange_isIso_iff_cartesian_comparison
    (f : X ⟶ Y) (q : Y ⟶ B) (g : T ⟶ B)
    (u : X' ⟶ X) (p : X' ⟶ T) (v : Y' ⟶ Y) (r : Y' ⟶ T) (k : X' ⟶ Y')
    (hX : IsPullback u p (f ≫ q) g) (hY : IsPullback v r q g)
    (hk : k ≫ v = u ≫ f) (hr : k ≫ r = p) :
    IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g) ↔ IsIso k := by
  have he : hX.isoPullback.inv ≫ k ≫ hY.isoPullback.hom = Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g := by
    apply pullback.hom_ext
    · calc
        (hX.isoPullback.inv ≫ k ≫ hY.isoPullback.hom) ≫ pullback.fst q g =
            hX.isoPullback.inv ≫ (k ≫ v) := by
          rw [Category.assoc, Category.assoc, hY.isoPullback_hom_fst]
        _ = hX.isoPullback.inv ≫ (u ≫ f) := by rw [hk]
        _ = pullback.fst (f ≫ q) g ≫ f := by
          rw [← Category.assoc, hX.isoPullback_inv_fst]
        _ = Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g ≫ pullback.fst q g := by
          simp only [Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange, pullback.map, pullback.lift_fst]
    · calc
        (hX.isoPullback.inv ≫ k ≫ hY.isoPullback.hom) ≫ pullback.snd q g =
            hX.isoPullback.inv ≫ (k ≫ r) := by
          rw [Category.assoc, Category.assoc, hY.isoPullback_hom_snd]
        _ = hX.isoPullback.inv ≫ p := by rw [hr]
        _ = pullback.snd (f ≫ q) g := hX.isoPullback_inv_snd
        _ = Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g ≫ pullback.snd q g := by
          simp only [Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange, pullback.map, pullback.lift_snd, Category.comp_id]
  rw [← he, isIso_comp_left_iff, isIso_comp_right_iff]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CartesianMorphismIsomorphismComparison
