import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FunctionFieldPoint

/-! # Function Field Open Point -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FunctionFieldOpenPoint

noncomputable section

/-! The common field-valued point factors through each homogeneous
chart; its evaluation of regular sections is the canonical chart-to-field map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (K : Type u) [Field K] {n : ℕ}
variable (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ≠ 0)
variable {d : ℕ} (hfd : f ∈ Hilbert.Polynomial.GradedHilbert.grading K n d) (hd : 0 < d)

def projectiveFunctionFieldOpenPoint :
    Spec (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))) ⟶
      (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) f).toScheme :=
  Spec.map (CommRingCat.ofHom (Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap K f hf)) ≫
    (Proj.basicOpenIsoSpec (Hilbert.Polynomial.GradedHilbert.grading K n) f hfd hd).inv

theorem projectiveFunctionFieldOpenPoint_inclusion :
    projectiveFunctionFieldOpenPoint K f hf hfd hd ≫ (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) f).ι =
      FunctionFieldPoint.projectiveFunctionFieldChartPoint K f hf hfd hd := Category.assoc _ _ _

theorem projectiveFunctionFieldOpenPoint_sections :
    (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) f).topIso.inv ≫
      (projectiveFunctionFieldOpenPoint K f hf hfd hd).appTop ≫
        (Scheme.ΓSpecIso (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))).hom =
      (Proj.basicOpenIsoAway (Hilbert.Polynomial.GradedHilbert.grading K n) f hfd hd).inv ≫
        CommRingCat.ofHom (Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap K f hf) := by
  let U := Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) f
  let R := CommRingCat.of (HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading K n) f)
  let e := Proj.basicOpenIsoSpec (Hilbert.Polynomial.GradedHilbert.grading K n) f hfd hd
  let b := Proj.basicOpenIsoAway (Hilbert.Polynomial.GradedHilbert.grading K n) f hfd hd
  let φ := CommRingCat.ofHom (Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap K f hf)
  have he : e.hom.appTop = (Scheme.ΓSpecIso R).hom ≫ b.hom ≫ U.topIso.inv :=
    Proj.basicOpenToSpec_app_top (Hilbert.Polynomial.GradedHilbert.grading K n) f
  have he' : (Scheme.ΓSpecIso R).inv ≫ e.hom.appTop = b.hom ≫ U.topIso.inv :=
    (Iso.inv_comp_eq (Scheme.ΓSpecIso R)).mpr he
  have hi : U.topIso.inv ≫ e.inv.appTop = b.inv ≫ (Scheme.ΓSpecIso R).inv := by
    apply (cancel_epi b.hom).mp
    rw [← Category.assoc, ← he', Category.assoc, ← Scheme.Hom.comp_appTop,
      Iso.inv_hom_id, Scheme.Hom.id_appTop, Category.comp_id, Iso.hom_inv_id_assoc]
  change U.topIso.inv ≫ (Spec.map φ ≫ e.inv).appTop ≫
      (Scheme.ΓSpecIso (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))).hom = b.inv ≫ φ
  rw [Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  rw [← Category.assoc U.topIso.inv e.inv.appTop, hi]
  simp only [Category.assoc]
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FunctionFieldOpenPoint
