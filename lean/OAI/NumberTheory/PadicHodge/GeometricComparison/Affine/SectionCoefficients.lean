import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CoordinateLocalization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech

/-! # Section Coefficients -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.SectionCoefficients.AffineCoordinates

noncomputable section

/-! Cohomology's actual section coefficients on an affine identity model agree with the canonical structure-sheaf coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (A : Type u) [CommRing A]

attribute [local instance] CoordinateLocalization.AffineCoordinates.sectionAlgebra

theorem sectionBaseMap_eq (U : (Spec (CommRingCat.of A)).Opens) :
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap A (AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech.AffineCech.model A) U =
      algebraMap A Γ(Spec (CommRingCat.of A), U) := by
  apply RingHom.ext
  intro a
  change ((Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of A))) ⊤ U le_top)
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = algebraMap A Γ(Spec (CommRingCat.of A), U) a
  have h : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of A))) ⊤ U le_top =
      CommRingCat.ofHom (algebraMap A Γ(Spec (CommRingCat.of A), U)) := by
    have hi : Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of A))) ⊤ U le_top =
        (Spec (CommRingCat.of A)).presheaf.map (homOfLE le_top).op := by
      change (𝟙 _) ≫ _ = _
      exact Category.id_comp _
    rw [hi]
    exact (Scheme.toOpen_eq (CommRingCat.of A) U).symm
  exact ConcreteCategory.congr_hom h a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.SectionCoefficients.AffineCoordinates
