import OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeSectionCoefficients
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Over Spec -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OverSpec.AffineOverSpec

noncomputable section

/-! Every actual affine scheme over the base is canonically its native relative spectrum of global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

local instance : Algebra R Γ(X.left, ⊤) := OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X ⊤

theorem appLE_top : X.hom.appLE ⊤ ⊤ le_top = X.hom.appTop := by
  change X.hom.appTop ≫ X.left.presheaf.map (𝟙 _) = X.hom.appTop
  rw [X.left.presheaf.map_id, Category.comp_id]

theorem coefficient_map : CommRingCat.ofHom (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X ⊤) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop := by
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appLE ⊤ ⊤ le_top = _
  rw [appLE_top]

theorem structure_square : X.left.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X ⊤)) = X.hom := by
  rw [coefficient_map, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

def model : Over (Spec (CommRingCat.of R)) :=
  RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R Γ(X.left, ⊤)

def iso [IsAffine X.left] : X ≅ model R X :=
  Over.isoMk X.left.isoSpec (by
    change X.left.toSpecΓ ≫ (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R Γ(X.left, ⊤)).hom = X.hom
    rw [RelativeSectionCoefficients.RelativeSpecMaps.structure_eq]
    exact structure_square R X)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OverSpec.AffineOverSpec
