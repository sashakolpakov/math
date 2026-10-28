import OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarRestrictionSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.PowerScalarLocalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FormMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormScalarExtension

/-! # Form Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FormLocalization

noncomputable section

/-!
# IntegralComparison: actual Frobenius differential-form restriction retains affine localization
-/

open _root_.CategoryTheory

universe u

variable {k : Type u} [Field k] [Fintype k] {A B : CommAlgCat.{u} k} (f : A ⟶ B) (n : ℕ)

def ordinaryMap : ModuleCat.of A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k A n) ⟶
    (ModuleCat.restrictScalars f.hom.toRingHom).obj (ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k B n)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k A n))
    (Y := (ModuleCat.restrictScalars f.hom.toRingHom).obj (ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k B n)))
    { toFun := fun ω => AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n ω
      map_add' := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n).map_add
      map_smul' := OrdinaryFormScalars.Ordinary.formMap_smul k A B f.hom n }

def restrictionIso :
    (ModuleCat.restrictScalars (FiniteField.frobeniusAlgHom k A).toRingHom).obj
      ((ModuleCat.restrictScalars f.hom.toRingHom).obj (ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k B n))) ≅
    (ModuleCat.restrictScalars f.hom.toRingHom).obj (DeRhamComplex.forms k B n) :=
  ScalarRestrictionSquare.iso f.hom.toRingHom (FiniteField.frobeniusAlgHom k A).toRingHom
    (FiniteField.frobeniusAlgHom k B).toRingHom (RingHom.ext (FormMaps.frobenius f))
    (ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k B n))

theorem map_eq :
    (ModuleCat.restrictScalars (FiniteField.frobeniusAlgHom k A).toRingHom).map (ordinaryMap f n) ≫
      (restrictionIso f n).hom = FormMaps.map f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  rfl

theorem isLocalizedModule (S : Submonoid A) [IsLocalizedModule S (ordinaryMap f n).hom] :
    IsLocalizedModule S (FormMaps.map f n).hom := by
  let : IsLocalizedModule S
      ((ModuleCat.restrictScalars (FiniteField.frobeniusAlgHom k A).toRingHom).map (ordinaryMap f n)).hom :=
    PowerScalarLocalization.isLocalizedModule (FiniteField.frobeniusAlgHom k A).toRingHom
      (Fintype.card k) (fun _ => rfl) Fintype.card_pos S (ordinaryMap f n)
  have h : IsLocalizedModule S ((restrictionIso f n).toLinearEquiv.toLinearMap.comp
      ((ModuleCat.restrictScalars (FiniteField.frobeniusAlgHom k A).toRingHom).map (ordinaryMap f n)).hom) :=
    IsLocalizedModule.of_linearEquiv S _ (restrictionIso f n).toLinearEquiv
  change IsLocalizedModule S
    (((ModuleCat.restrictScalars (FiniteField.frobeniusAlgHom k A).toRingHom).map (ordinaryMap f n) ≫
      (restrictionIso f n).hom).hom) at h
  rw [map_eq] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FormLocalization
