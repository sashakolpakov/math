import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ChartPullback

/-! # Projective Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectivePullback

noncomputable section

/-! The relative projective coefficient square is a genuine scheme
pullback, proved on the native finite polynomial coordinate cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Base

theorem isPullback {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    IsPullback (ProjectiveI.Scalars.map f n) (ProjectiveI.Base.base S n)
      (ProjectiveI.Base.base R n) (Spec.map (CommRingCat.ofHom f)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (ChartPullback.cover R n)
  intro i
  let hc := (ChartPullback.chart f n i).flip
  let hp := Polynomial.ScalarPullback.isPullback f {j : Fin (n + 1) // j ≠ i}
  change IsPullback
    (pullback.snd (ProjectiveI.Scalars.map f n) (ChartX.Projective.projectiveAffineChartMap R n i))
    (pullback.fst (ProjectiveI.Scalars.map f n) (ChartX.Projective.projectiveAffineChartMap R n i) ≫ ProjectiveI.Base.base S n)
    (ChartX.Projective.projectiveAffineChartMap R n i ≫ ProjectiveI.Base.base R n) (Spec.map (CommRingCat.ofHom f))
  refine hp.of_iso hc.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.refl_hom, Category.comp_id] using hc.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, hc.isoPullback_hom_fst, ChartX.Projective.projectiveAffineChartMap_over]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, ChartX.Projective.projectiveAffineChartMap_over]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectivePullback
