import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AwayChartPullback
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart

/-! # Chart Fractions -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartFractions

noncomputable section

/-! On its defining affine charts, a linear projection pulls a
ratio of target coordinates back to the corresponding ratio of linear forms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

theorem spec_germ {A B : CommRingCat} (f : A ⟶ B) (x : Spec B) (a : A) :
    (Spec.map f).stalkMap x ((Spec A).presheaf.germ ⊤ (Spec.map f x) trivial ((Scheme.ΓSpecIso A).inv a)) =
      (Spec B).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso B).inv (f a)) := by
  rw [GermPullback.appLE (Spec.map f) ⊤ ⊤ le_top x trivial]
  exact congrArg ((Spec B).presheaf.germ ⊤ x trivial)
    (congrArg (fun g : A ⟶ Γ(Spec B, ⊤) => g a) (Scheme.ΓSpecIso_inv_naturality f).symm)

variable {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
  (s a : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1)

abbrev image (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 := ⟨f a.val, f.map_mem a.property⟩

theorem affine (x : Spec (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s.val))))
    (hs : s.val ∉ (Projective.LinearChart.Hom.affine f s.val s.property (by decide : 0 < 1) x).asHomogeneousIdeal) :
    GermPullback.fraction m
      (Projective.LinearChart.Hom.affine f s.val s.property (by decide : 0 < 1)) x a s hs =
    GermPullback.fraction n (AwayChartPullback.chart n (image f s)) x
      (image f a) (image f s) (AwayChartPullback.contained n (image f s) trivial) := by
  change GermPullback.fraction m
    (Spec.map (CommRingCat.ofHom (Away.map f s.val)) ≫ AwayChartPullback.chart m s) x a s hs = _
  rw [GermPullback.fraction_comp, AwayChartPullback.fraction, spec_germ,
    AwayChartPullback.fraction]
  exact congrArg (fun b : Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s.val) =>
    (Spec (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s.val)))).presheaf.germ ⊤ x trivial
      ((Scheme.ΓSpecIso (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s.val)))).inv b))
    (Away.map_mk f s.val s.property 1 a.val a.property)

theorem chart (x : (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s.val)).toScheme)
    (hs : s.val ∉ (Projective.LinearChart.Hom.chart f s.val s.property (by decide : 0 < 1) x).asHomogeneousIdeal) :
    GermPullback.fraction m
      (Projective.LinearChart.Hom.chart f s.val s.property (by decide : 0 < 1)) x a s hs =
    GermPullback.fraction n (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s.val)).ι x
      (image f a) (image f s) x.property := by
  let U := Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s.val)
  let e := Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s.val) (f.map_mem s.property) (by decide : 0 < 1)
  have he : e.hom ≫ AwayChartPullback.chart n (image f s) = U.ι := by
    change e.hom ≫ (e.inv ≫ U.ι) = U.ι
    simp
  change GermPullback.fraction m
    (e.hom ≫ Projective.LinearChart.Hom.affine f s.val s.property (by decide : 0 < 1)) x a s hs = _
  rw [GermPullback.fraction_comp]
  calc
    _ = e.hom.stalkMap x (GermPullback.fraction n (AwayChartPullback.chart n (image f s))
        (e.hom x) (image f a) (image f s)
        (AwayChartPullback.contained n (image f s) trivial)) :=
      congrArg (e.hom.stalkMap x) (affine f s a (e.hom x) hs)
    _ = _ := by
      rw [← GermPullback.fraction_comp]
      exact GermPullback.fraction_congr n _ _ he x (image f a) (image f s) _ _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartFractions
