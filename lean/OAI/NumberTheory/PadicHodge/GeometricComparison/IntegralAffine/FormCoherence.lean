import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormModules
import OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafLocalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialFormFiniteness

/-! # Form Coherence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormCoherence.IntegralAffineFormCoherence

noncomputable section

/-! Native zero- and one-form modules are coherent on affine schemes of finite type over any base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormModules.IntegralAffineFormModules

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]

theorem localization_transport
    (P : (Spec (CommRingCat.of A)).Opensᵒᵖ ⥤ ModuleCat A)
    (n : ℕ) (hn : n ≤ 1) (a : A)
    (e : P ≅ Affine.FormsCech.CoordinateForms.specPresheaf R A n) :
    IsLocalizedModule (Submonoid.powers a)
      (P.map (PrimeSpectrum.basicOpen a).leTop.op).hom := by
  let := Integral.LowDegreeCoordinateForms.IntegralLowDegreeCoordinateForms.specPresheaf_isLocalized R A n hn a
  exact PresheafLocalization.PresheafLocalizationTransport.isLocalized e
    (PrimeSpectrum.basicOpen a).leTop.op (Submonoid.powers a)

theorem localized (n : ℕ) (hn : n ≤ 1) (a : A) :
    IsLocalizedModule (Submonoid.powers a)
      ((FormModules.IntegralAffineFormModules.scalars R A n).map (PrimeSpectrum.basicOpen a).leTop.op).hom :=
  localization_transport R A (FormModules.IntegralAffineFormModules.scalars R A n) n hn a (FormModules.IntegralAffineFormModules.iso R A n)

theorem quasicoherent (n : ℕ) (hn : n ≤ 1) :
    (Integral.FormsModules.IntegralFormsModules.sheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n).IsQuasicoherent :=
  IntegralComparison.Affine.LocalizingModule.quasicoherent A
    (Integral.FormsModules.IntegralFormsModules.presheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n) (localized R A n hn)

theorem coordinate_finite_top [Algebra.FiniteType R A] (n : ℕ) :
    Module.Finite A ((Affine.FormsCech.CoordinateForms.specPresheaf R A n).obj (op ⊤)) := by
  let := RelativeFormsFunctor.CoordinateForms.coordinateAlgebra R A
  let B := (Affine.CoordinateLocalization.AffineCoordinates.algebras A).obj (op ⊤)
  let : Algebra R B := RelativeFormsFunctor.CoordinateForms.baseAlgebra R A B
  change Module.Finite A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n)
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite A B := Module.Finite.of_surjective (Algebra.linearMap A B)
    StructureSheaf.algebraMap_obj_top_bijective.surjective
  let : Algebra.FiniteType R B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  let : Module.Finite B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) := IntegralComparison.DifferentialFormFiniteness.forms_finite R B n
  let : IsScalarTower A B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) := by
    change IsScalarTower A B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw B n ⧸ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R B n)
    infer_instance
  exact Module.Finite.trans B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n)

theorem finite_top [Algebra.FiniteType R A] (n : ℕ) :
    Module.Finite A ((FormModules.IntegralAffineFormModules.scalars R A n).obj (op ⊤)) := by
  let := coordinate_finite_top R A n
  exact Module.Finite.equiv ((FormModules.IntegralAffineFormModules.iso R A n).app (op ⊤)).toLinearEquiv.symm

theorem finiteType [Algebra.FiniteType R A] (n : ℕ) (hn : n ≤ 1) :
    (Integral.FormsModules.IntegralFormsModules.sheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n).IsFiniteType := by
  let : Module.Finite A ((IntegralComparison.Affine.LocalizingModule.scalars A
      (Integral.FormsModules.IntegralFormsModules.presheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n)).obj (op ⊤)) := finite_top R A n
  exact IntegralComparison.Affine.LocalizingModule.finiteType A
    (Integral.FormsModules.IntegralFormsModules.presheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n) (localized R A n hn)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormCoherence.IntegralAffineFormCoherence
