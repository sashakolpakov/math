import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GermPullback

/-! # Away Chart Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AwayChartPullback

noncomputable section

/-! Pulling a homogeneous fraction back along the corresponding
affine chart gives the germ of that element of the chart ring. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

variable (n : ℕ) (s : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)

abbrev chart := Proj.awayι (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val s.property (by decide : 0 < 1)

theorem contained : (⊤ : (Spec (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val))).Opens) ≤
    chart n s ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val := by
  intro x _
  exact ((Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val s.property (by decide : 0 < 1)).inv x).property

theorem appLE :
    (chart n s).appLE (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val) ⊤ (contained n s) =
      (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val).topIso.inv ≫
        (Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val s.property (by decide : 0 < 1)).inv.appTop := by
  let U := Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val
  let e := Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val s.property (by decide : 0 < 1)
  have hU : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun x _ => x.property
  exact (Scheme.Hom.appLE_comp_appLE e.inv U.ι U ⊤ ⊤ hU le_top).symm

theorem sections_pullback :
    Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val ≫
      (chart n s).appLE (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val) ⊤ (contained n s) =
        (Scheme.ΓSpecIso (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val))).inv := by
  let e := Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val s.property (by decide : 0 < 1)
  apply (cancel_epi (Scheme.ΓSpecIso (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val))).hom).mp
  have he : e.hom.appTop = (Scheme.ΓSpecIso (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val))).hom ≫
      Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val ≫
        (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val).topIso.inv :=
    Proj.basicOpenToSpec_app_top (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val
  rw [AwayChartPullback.appLE]
  calc
    _ = e.hom.appTop ≫ e.inv.appTop := by rw [he]; simp only [Category.assoc]; rfl
    _ = _ := by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]; simp

theorem fraction (x : Spec (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val)))
    (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    GermPullback.fraction n (chart n s) x a s (contained n s (by trivial)) =
      (Spec (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val))).presheaf.germ ⊤ x trivial
        ((Scheme.ΓSpecIso (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val))).inv
          (Away.mk (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.property 1 a.val a.property)) := by
  change (chart n s).stalkMap x _ = _
  rw [← Projective.PointJets.StalkFractions.germ,
    GermPullback.appLE (chart n s) _ ⊤ (contained n s) x trivial]
  exact congrArg ((Spec (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val))).presheaf.germ ⊤ x trivial)
    (congrArg (fun f : CommRingCat.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val) ⟶
      Γ(Spec (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val)), ⊤) =>
        f (Away.mk (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.property 1 a.val a.property)) (sections_pullback n s))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AwayChartPullback
