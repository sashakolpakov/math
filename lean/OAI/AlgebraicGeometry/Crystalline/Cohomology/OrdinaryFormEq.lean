import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormScalarExtension

/-! # Ordinary Form Eq -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormEq.OrdinaryFormScalarLocalization

noncomputable section

/-! # Ordinary form pullback localizes with the actual restricted target action -/

open _root_.CategoryTheory

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

def targetIso (n : ℕ) : ModuleCat.of A (DeRhamPresentationTo.DeRhamPresentation.Form R B n) ≅
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (DeRhamPresentationTo.DeRhamPresentation.Form R B n)) :=
  (AddEquiv.toLinearEquiv
    (M := ↑(ModuleCat.of A (DeRhamPresentationTo.DeRhamPresentation.Form R B n)))
    (M₂ := ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (DeRhamPresentationTo.DeRhamPresentation.Form R B n))))
    (by rfl) (fun a x => (algebraMap_smul B a (show DeRhamPresentationTo.DeRhamPresentation.Form R B n from x)).symm)).toModuleIso

theorem map_eq (n : ℕ) : ModuleCat.ofHom (NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars.Ordinary.map R A B n) ≫
    (targetIso R A B n).hom =
      OrdinaryFormBase.OrdinaryFormModulePresheaf.formMap R (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

variable (σ : Type u) [LinearOrder σ]
  [Algebra (MvPolynomial σ R) A] [Algebra (MvPolynomial σ R) B]
  [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B]
  [IsScalarTower (MvPolynomial σ R) A B]
  [Algebra.FormallyEtale (MvPolynomial σ R) A] [Algebra.FormallyEtale (MvPolynomial σ R) B]

include σ in
theorem localized (S : Submonoid A) [IsLocalization S B] (n : ℕ) :
    IsLocalizedModule S (OrdinaryFormBase.OrdinaryFormModulePresheaf.formMap R
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) n).hom := by
  let : IsLocalizedModule S (NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars.Ordinary.map R A B n) :=
    NumberTheory.PadicHodge.IntegralComparison.Etale.FormScalarExtension.isLocalizedModule R A B σ S n
  have h := IsLocalizedModule.of_linearEquiv S (NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars.Ordinary.map R A B n)
    (targetIso R A B n).toLinearEquiv
  change IsLocalizedModule S ((ModuleCat.ofHom (NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars.Ordinary.map R A B n) ≫
    (targetIso R A B n).hom).hom) at h
  rw [map_eq] at h
  exact h

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormEq.OrdinaryFormScalarLocalization
