import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.SectionCoefficients
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarFormsChange

/-! # Relative Section Coefficients -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.RelativeSectionCoefficients.AffineCoordinates

/-! The native coefficients on a relative affine spectrum are the actual composite of the base and coordinate-ring maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]

attribute [local instance] Affine.CoordinateLocalization.AffineCoordinates.sectionAlgebra

def relativeSpecModel : Over (Spec (CommRingCat.of R)) :=
  ScalarFormsChange.SectionScalarChange.restrictBase (algebraMap R A) (AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech.AffineCech.model A)

theorem relative_sectionBaseMap_eq (U : (Spec (CommRingCat.of A)).Opens) :
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R (relativeSpecModel R A) U =
      (algebraMap A Γ(Spec (CommRingCat.of A), U)).comp (algebraMap R A) :=
  (ScalarFormsChange.SectionScalarChange.sectionBaseMap_comp (algebraMap R A) (AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech.AffineCech.model A) U).trans
    (congrArg (fun f : A →+* Γ(Spec (CommRingCat.of A), U) => f.comp (algebraMap R A))
      (Affine.SectionCoefficients.AffineCoordinates.sectionBaseMap_eq A U))

end NumberTheory.PadicHodge.GeometricComparison.RelativeSectionCoefficients.AffineCoordinates

namespace NumberTheory.PadicHodge.GeometricComparison.RelativeSectionCoefficients.RelativeSpecMaps

/-! Actual homomorphisms of base algebras induce morphisms between the native relative affine models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]

theorem structure_eq : (AffineCoordinates.relativeSpecModel R A).hom =
    Spec.map (CommRingCat.ofHom (algebraMap R A)) := Category.id_comp _

variable {R A} {B : Type} [CommRing B] [Algebra R B]

theorem spec_condition (f : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  have h : CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom f.toRingHom =
      CommRingCat.ofHom (algebraMap R B) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext f.commutes
  exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom f.toRingHom)).symm.trans
    (congrArg Spec.map h)

def map (f : A →ₐ[R] B) : AffineCoordinates.relativeSpecModel R B ⟶
    AffineCoordinates.relativeSpecModel R A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    exact (congrArg (fun g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) =>
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g) (structure_eq R A)).trans
        ((spec_condition f).trans (structure_eq R B).symm))

theorem map_left (f : A →ₐ[R] B) : (RelativeSpecMaps.map f).left = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

end NumberTheory.PadicHodge.GeometricComparison.RelativeSectionCoefficients.RelativeSpecMaps

end

end OAI
