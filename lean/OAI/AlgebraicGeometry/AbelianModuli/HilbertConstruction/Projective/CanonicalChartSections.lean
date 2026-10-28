import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.SectionCoordinates

/-! # Canonical Chart Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CanonicalChartSections

noncomputable section

/-! The affine-chart coefficient coordinates agree with the canonical homogeneous-localization sections of a projective basic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem commRingIso_apply_of_inv_eq {B C : CommRingCat.{u}} (e : B ≅ C) (f : C ⟶ B)
    (h : e.inv = f) (z : C) : e.hom (f z) = z := by
  subst f
  exact ConcreteCategory.congr_hom e.inv_hom_id z

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem projectiveAffineChartSectionsIso_inv {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    (Affine.ChartCoefficientSections.affineChartSectionsIso (Proj.basicOpen 𝒜 s) (Proj.basicOpenIsoSpec 𝒜 s hs hd).symm).inv =
      Proj.awayToSection 𝒜 s := by
  have he : (Proj.basicOpenIsoSpec 𝒜 s hs hd).hom.appTop =
      (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 s))).hom ≫
        Proj.awayToSection 𝒜 s ≫ (Proj.basicOpen 𝒜 s).topIso.inv := Proj.basicOpenToSpec_app_top 𝒜 s
  change (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 s))).inv ≫
    (Proj.basicOpenIsoSpec 𝒜 s hs hd).hom.appTop ≫ (Proj.basicOpen 𝒜 s).topIso.hom = _
  rw [he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem projectiveAffineChartSectionsIso_awayToSection {d : ℕ} {s : A}
    (hs : s ∈ 𝒜 d) (hd : 0 < d) (z : HomogeneousLocalization.Away 𝒜 s) :
    (Affine.ChartCoefficientSections.affineChartSectionsIso (Proj.basicOpen 𝒜 s) (Proj.basicOpenIsoSpec 𝒜 s hs hd).symm).hom
      (Proj.awayToSection 𝒜 s z) = z := by
  exact commRingIso_apply_of_inv_eq
    (Affine.ChartCoefficientSections.affineChartSectionsIso (Proj.basicOpen 𝒜 s) (Proj.basicOpenIsoSpec 𝒜 s hs hd).symm)
    (Proj.awayToSection 𝒜 s) (projectiveAffineChartSectionsIso_inv 𝒜 hs hd) z

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CanonicalChartSections
