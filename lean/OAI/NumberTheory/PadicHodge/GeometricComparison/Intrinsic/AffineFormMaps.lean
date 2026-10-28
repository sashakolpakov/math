import OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeSectionCoefficients
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoefficientIdentity
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoefficientRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.FormsCech

/-! # Affine Form Maps -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormMaps.AffineCoordinates

noncomputable section

section

/-! The native Cohomology forms on a relative affine spectrum identify with the actual coordinate-form modules after restricting scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]

attribute [local instance] Affine.CoordinateLocalization.AffineCoordinates.sectionAlgebra

@[instance_reducible]
def coordinateBaseAlgebra (U : (Spec (CommRingCat.of A)).Opens) :
    Algebra R Γ(Spec (CommRingCat.of A), U) :=
  ((algebraMap A Γ(Spec (CommRingCat.of A), U)).comp (algebraMap R A)).toAlgebra

theorem nativeSectionAlgebra_eq (U : (Spec (CommRingCat.of A)).Opens) :
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U = coordinateBaseAlgebra R A U :=
  Algebra.algebra_ext _ _ (fun r => DFunLike.congr_fun (RelativeSectionCoefficients.AffineCoordinates.relative_sectionBaseMap_eq R A U) r)

theorem nativeFormsModuleIso_exists (U : (Spec (CommRingCat.of A)).Opens) (n : ℕ) :
    ∃ e : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n).obj (Opposite.op U) ≅
      (ModuleCat.restrictScalars (algebraMap R A)).obj
        ((Affine.FormsCech.CoordinateForms.specPresheaf R A n).obj (Opposite.op U)),
      ∀ (b : Γ(Spec (CommRingCat.of A), U)) (v : Fin n → Γ(Spec (CommRingCat.of A), U)),
        e.hom (@AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(Spec (CommRingCat.of A), U) _ _
          (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U) n b v) =
          @AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(Spec (CommRingCat.of A), U) _ _
            (coordinateBaseAlgebra R A U) n b v := by
  let B := Γ(Spec (CommRingCat.of A), U)
  let α : Algebra R B := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U
  let β : Algebra R B := coordinateBaseAlgebra R A U
  let : Algebra R B := β
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Forms.CoefficientRestriction.FormsCoefficientRestriction.exists_iso_symbols R A B α (nativeSectionAlgebra_eq R A U) n

def nativeFormsModuleIso (U : (Spec (CommRingCat.of A)).Opens) (n : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n).obj (Opposite.op U) ≅
      (ModuleCat.restrictScalars (algebraMap R A)).obj
        ((Affine.FormsCech.CoordinateForms.specPresheaf R A n).obj (Opposite.op U)) :=
  (nativeFormsModuleIso_exists R A U n).choose

theorem nativeFormsModuleIso_symbol (U : (Spec (CommRingCat.of A)).Opens) (n : ℕ)
    (b : Γ(Spec (CommRingCat.of A), U)) (v : Fin n → Γ(Spec (CommRingCat.of A), U)) :
    (nativeFormsModuleIso R A U n).hom
      (@AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(Spec (CommRingCat.of A), U) _ _
        (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U) n b v) =
      @AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(Spec (CommRingCat.of A), U) _ _
        (coordinateBaseAlgebra R A U) n b v :=
  (nativeFormsModuleIso_exists R A U n).choose_spec b v

end

/-! Actual restriction maps on native and coordinate affine forms have identical differential-symbol formulas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]

attribute [local instance] Affine.CoordinateLocalization.AffineCoordinates.sectionAlgebra

def nativeSymbol (U : (Spec (CommRingCat.of A)).Opens) (n : ℕ)
    (b : Γ(Spec (CommRingCat.of A), U)) (v : Fin n → Γ(Spec (CommRingCat.of A), U)) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n).obj (op U) :=
  @AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(Spec (CommRingCat.of A), U) _ _
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U) n b v

def coordinateSymbol (U : (Spec (CommRingCat.of A)).Opens) (n : ℕ)
    (b : Γ(Spec (CommRingCat.of A), U)) (v : Fin n → Γ(Spec (CommRingCat.of A), U)) :
    (Affine.FormsCech.CoordinateForms.specPresheaf R A n).obj (op U) :=
  @AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(Spec (CommRingCat.of A), U) _ _
    (coordinateBaseAlgebra R A U) n b v

theorem nativeSymbol_map {U V : (Spec (CommRingCat.of A)).Opens} (f : op U ⟶ op V)
    (n : ℕ) (b : Γ(Spec (CommRingCat.of A), U)) (v : Fin n → Γ(Spec (CommRingCat.of A), U)) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n).map f (nativeSymbol R A U n b v) =
      nativeSymbol R A V n ((Spec (CommRingCat.of A)).presheaf.map f b)
        (fun i => (Spec (CommRingCat.of A)).presheaf.map f (v i)) :=
  AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)).map f) n b v

theorem coordinateSymbol_map {U V : (Spec (CommRingCat.of A)).Opens} (f : op U ⟶ op V)
    (n : ℕ) (b : Γ(Spec (CommRingCat.of A), U)) (v : Fin n → Γ(Spec (CommRingCat.of A), U)) :
    (Affine.FormsCech.CoordinateForms.specPresheaf R A n).map f (coordinateSymbol R A U n b v) =
      coordinateSymbol R A V n ((Spec (CommRingCat.of A)).presheaf.map f b)
        (fun i => (Spec (CommRingCat.of A)).presheaf.map f (v i)) :=
  RelativeFormsFunctor.CoordinateForms.formMap_symbol R A ((Affine.CoordinateLocalization.AffineCoordinates.algebras A).map f) n b v

theorem nativeSymbol_comparison (U : (Spec (CommRingCat.of A)).Opens) (n : ℕ)
    (b : Γ(Spec (CommRingCat.of A), U)) (v : Fin n → Γ(Spec (CommRingCat.of A), U)) :
    (nativeFormsModuleIso R A U n).hom (nativeSymbol R A U n b v) = coordinateSymbol R A U n b v :=
  nativeFormsModuleIso_symbol R A U n b v

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormMaps.AffineCoordinates
