import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Towers

/-! # Coordinate Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoordinateSections

noncomputable section

/-!
# IntegralComparison: native affine coordinate scalars agree with principal-open localization
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

private theorem localization_of_algebra_eq {R A : Type u} [CommRing R] [CommRing A]
    (S : Submonoid R) (a b : Algebra R A) (h : a = b)
    (hb : letI := b; IsLocalization S A) : letI := a; IsLocalization S A :=
  h.symm ▸ hb

variable (C : Type u) [CommRing C]

theorem algebra_eq (U : (Spec (CommRingCat.of C)).Opens) :
    AffineSection.Towers.coordinateAlgebra C U = StructureSheaf.openAlgebra C (op U) := by
  apply Algebra.algebra_ext
  intro c
  change AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap C (ModuleScalars.base C) U c = _
  rw [ModuleScalars.baseMap]
  exact ConcreteCategory.congr_hom (Scheme.toOpen_eq (CommRingCat.of C) U).symm c

theorem principal_localization (c : C) :
    letI : Algebra C Γ(Spec (CommRingCat.of C), PrimeSpectrum.basicOpen c) :=
      AffineSection.Towers.coordinateAlgebra C (PrimeSpectrum.basicOpen c)
    IsLocalization.Away c Γ(Spec (CommRingCat.of C), PrimeSpectrum.basicOpen c) := by
  exact localization_of_algebra_eq (Submonoid.powers c) _ _
    (algebra_eq C (PrimeSpectrum.basicOpen c)) (StructureSheaf.IsLocalization.to_basicOpen C c)

theorem global_bijective :
    letI : Algebra C Γ(Spec (CommRingCat.of C), ⊤) := AffineSection.Towers.coordinateAlgebra C ⊤
    Function.Bijective (algebraMap C Γ(Spec (CommRingCat.of C), ⊤)) := by
  rw [algebra_eq]
  exact StructureSheaf.algebraMap_obj_top_bijective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoordinateSections
