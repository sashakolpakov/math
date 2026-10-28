import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoordinateCoefficientIdentity
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeCoordinateForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalizingModule
import OAI.NumberTheory.PadicHodge.GeometricComparison.FormSymbol

/-! # Form Modules -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormModules.IntegralAffineFormModules

noncomputable section

/-! Native affine form modules have the canonical coordinate-module presheaf and low-degree localization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormMaps.AffineCoordinates

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]

def scalars (n : ℕ) : (Spec (CommRingCat.of A)).Opensᵒᵖ ⥤ ModuleCat A :=
  (IntegralComparison.AlgebraSheafScalars.presheaves A (IntegralComparison.Affine.ModuleScalars.base A)).obj
    (Integral.FormsModules.IntegralFormsModules.presheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n)

theorem coordinateAlgebra_eq (U : (Spec (CommRingCat.of A)).Opens) :
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra A (IntegralComparison.Affine.ModuleScalars.base A) U = Affine.CoordinateLocalization.AffineCoordinates.sectionAlgebra A U :=
  Algebra.algebra_ext _ _ (fun r => DFunLike.congr_fun (Affine.SectionCoefficients.AffineCoordinates.sectionBaseMap_eq A U) r)

def component (n : ℕ) (U : (Spec (CommRingCat.of A)).Opens) :
    (scalars R A n).obj (op U) ≅ (Affine.FormsCech.CoordinateForms.specPresheaf R A n).obj (op U) :=
  Forms.CoordinateCoefficientIdentity.FormsCoordinateCoefficientIdentity.iso R A Γ(Spec (CommRingCat.of A), U)
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U) (Intrinsic.AffineFormMaps.AffineCoordinates.coordinateBaseAlgebra R A U)
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra A (IntegralComparison.Affine.ModuleScalars.base A) U) (Affine.CoordinateLocalization.AffineCoordinates.sectionAlgebra A U)
    (Intrinsic.AffineFormMaps.AffineCoordinates.nativeSectionAlgebra_eq R A U) (coordinateAlgebra_eq A U) n

theorem component_symbol (n : ℕ) (U : (Spec (CommRingCat.of A)).Opens)
    (b : Γ(Spec (CommRingCat.of A), U)) (v : Fin n → Γ(Spec (CommRingCat.of A), U)) :
    (component R A n U).hom (Intrinsic.AffineFormMaps.AffineCoordinates.nativeSymbol R A U n b v) = Intrinsic.AffineFormMaps.AffineCoordinates.coordinateSymbol R A U n b v :=
  Forms.CoordinateCoefficientIdentity.FormsCoordinateCoefficientIdentity.iso_symbol R A Γ(Spec (CommRingCat.of A), U)
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U) (Intrinsic.AffineFormMaps.AffineCoordinates.coordinateBaseAlgebra R A U)
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra A (IntegralComparison.Affine.ModuleScalars.base A) U) (Affine.CoordinateLocalization.AffineCoordinates.sectionAlgebra A U)
    (Intrinsic.AffineFormMaps.AffineCoordinates.nativeSectionAlgebra_eq R A U) (coordinateAlgebra_eq A U) n b v

theorem scalars_map_symbol {U V : (Spec (CommRingCat.of A)).Opens} (f : op U ⟶ op V)
    (n : ℕ) (b : Γ(Spec (CommRingCat.of A), U)) (v : Fin n → Γ(Spec (CommRingCat.of A), U)) :
    (scalars R A n).map f (Intrinsic.AffineFormMaps.AffineCoordinates.nativeSymbol R A U n b v) =
      Intrinsic.AffineFormMaps.AffineCoordinates.nativeSymbol R A V n ((Spec (CommRingCat.of A)).presheaf.map f b)
        (fun i => (Spec (CommRingCat.of A)).presheaf.map f (v i)) :=
  Intrinsic.AffineFormMaps.AffineCoordinates.nativeSymbol_map R A f n b v

def iso (n : ℕ) : scalars R A n ≅ Affine.FormsCech.CoordinateForms.specPresheaf R A n :=
  NatIso.ofComponents (fun U => component R A n U.unop) (by
    intro U V f
    apply ModuleCat.hom_ext
    let : Algebra R Γ(Spec (CommRingCat.of A), U.unop) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U.unop
    apply LinearMap.toAddMonoidHom_injective
    apply FormSymbol.FormSymbolAdditiveExt.ext R Γ(Spec (CommRingCat.of A), U.unop) n
    intro b v
    change (component R A n V.unop).hom
      ((scalars R A n).map f (Intrinsic.AffineFormMaps.AffineCoordinates.nativeSymbol R A U.unop n b v)) =
        (Affine.FormsCech.CoordinateForms.specPresheaf R A n).map f
          ((component R A n U.unop).hom (Intrinsic.AffineFormMaps.AffineCoordinates.nativeSymbol R A U.unop n b v))
    rw [scalars_map_symbol, component_symbol, component_symbol, Intrinsic.AffineFormMaps.AffineCoordinates.coordinateSymbol_map])

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormModules.IntegralAffineFormModules
