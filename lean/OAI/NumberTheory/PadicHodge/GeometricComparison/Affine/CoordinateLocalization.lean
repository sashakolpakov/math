import OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-! # Coordinate Localization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CoordinateLocalization.AffineCoordinates

noncomputable section

/-! The actual coordinate-ring restriction from an affine spectrum to a principal open is a module localization over its affine base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (A : Type u) [CommRing A]

local instance sectionAlgebra (U : (Spec (CommRingCat.of A)).Opens) :
    Algebra A Γ(Spec (CommRingCat.of A), U) :=
  StructureSheaf.openAlgebra A (op U)

def algebras : (Spec (CommRingCat.of A)).Opensᵒᵖ ⥤ CommAlgCat.{u} A where
  obj U := CommAlgCat.of A Γ(Spec (CommRingCat.of A), U.unop)
  map f := CommAlgCat.ofHom
    { ((Spec (CommRingCat.of A)).presheaf.map f).hom with
      commutes' a := ConcreteCategory.congr_hom (StructureSheaf.algebraMap_self_map A _ _ f) a }
  map_id U := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact ConcreteCategory.congr_hom ((Spec (CommRingCat.of A)).presheaf.map_id U) x
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact ConcreteCategory.congr_hom ((Spec (CommRingCat.of A)).presheaf.map_comp f g) x

def principalRestriction (a : A) :
    op (⊤ : (Spec (CommRingCat.of A)).Opens) ⟶
      op (PrimeSpectrum.basicOpen a : (Spec (CommRingCat.of A)).Opens) :=
  (homOfLE (show (PrimeSpectrum.basicOpen a : (Spec (CommRingCat.of A)).Opens) ≤ ⊤ from le_top)).op

theorem principal_restriction_isLocalized (a : A) :
    IsLocalizedModule (Submonoid.powers a)
      ((algebras A).map (PrimeSpectrum.basicOpen a).leTop.op).hom.toLinearMap := by
  let : IsLocalization.Away a ((algebras A).obj (op (PrimeSpectrum.basicOpen a))) :=
    StructureSheaf.IsLocalization.to_basicOpen A a
  let f := ((algebras A).map (PrimeSpectrum.basicOpen a).leTop.op).hom.toLinearMap
  let e := Algebra.linearMap A ((algebras A).obj (op ⊤))
  have he : Function.Bijective e := by
    change Function.Bijective (StructureSheaf.toOpenₗ A A ⊤)
    exact StructureSheaf.toOpenₗ_top_bijective
  have hc : f.comp e = Algebra.linearMap A ((algebras A).obj (op (PrimeSpectrum.basicOpen a))) := by
    apply LinearMap.ext
    intro x
    exact ((algebras A).map (PrimeSpectrum.basicOpen a).leTop.op).hom.commutes x
  have hl : IsLocalizedModule (Submonoid.powers a) (f.comp e) := by
    rw [hc]
    infer_instance
  exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers a) e he).mp hl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CoordinateLocalization.AffineCoordinates
