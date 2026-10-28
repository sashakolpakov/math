import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FormLocalization

/-! # Etale Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.EtaleLocalization

noncomputable section

/-!
# IntegralComparison: Frobenius differential forms localize on the original étale-coordinate charts
-/

open _root_.CategoryTheory

universe u

variable (k C D σ : Type u) [Field k] [Fintype k] [CommRing C] [CommRing D] [LinearOrder σ]
  [Algebra k C] [Algebra k D] [Algebra C D] [IsScalarTower k C D]
  [Algebra (MvPolynomial σ k) C] [Algebra (MvPolynomial σ k) D]
  [IsScalarTower k (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) D]
  [IsScalarTower (MvPolynomial σ k) C D]
  [Algebra.FormallyEtale (MvPolynomial σ k) C] [Algebra.FormallyEtale (MvPolynomial σ k) D]

def targetIso (n : ℕ) : ModuleCat.of C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k D n) ≅
    (ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k D n)) :=
  (AddEquiv.toLinearEquiv
    (M := ↑(ModuleCat.of C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k D n)))
    (M₂ := ↑((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k D n))))
    (by rfl) (fun r x => (algebraMap_smul D r (show AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k D n from x)).symm)).toModuleIso

omit [Fintype k] in
theorem ordinaryMap_eq (n : ℕ) : ModuleCat.ofHom (OrdinaryFormScalars.Ordinary.map k C D n) ≫
    (targetIso k C D n).hom = FormLocalization.ordinaryMap
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k C D)) n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  rfl

include σ in
theorem isLocalizedModule (S : Submonoid C) [IsLocalization S D] (n : ℕ) :
    IsLocalizedModule S (FormMaps.map
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k C D)) n).hom := by
  let : IsLocalizedModule S (OrdinaryFormScalars.Ordinary.map k C D n) :=
    Etale.FormScalarExtension.isLocalizedModule k C D σ S n
  have h : IsLocalizedModule S ((targetIso k C D n).toLinearEquiv.toLinearMap.comp
      (OrdinaryFormScalars.Ordinary.map k C D n)) :=
    IsLocalizedModule.of_linearEquiv S _ (targetIso k C D n).toLinearEquiv
  change IsLocalizedModule S ((ModuleCat.ofHom (OrdinaryFormScalars.Ordinary.map k C D n) ≫
    (targetIso k C D n).hom).hom) at h
  rw [ordinaryMap_eq] at h
  let : IsLocalizedModule S (FormLocalization.ordinaryMap
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k C D)) n).hom := h
  exact FormLocalization.isLocalizedModule
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom k C D)) n S

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.EtaleLocalization
