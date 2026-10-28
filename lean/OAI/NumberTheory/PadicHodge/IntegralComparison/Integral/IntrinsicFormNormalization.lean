import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormSections

/-! # Intrinsic Form Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.IntrinsicFormNormalization.Intrinsic

noncomputable section

/-! The structure-module form sheaf and original base-module de Rham
sheaf have the same literal differential-symbol unit under their canonical
sheafification comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (U : X.left.Opens) (n : ℕ)

def iso :
    ((AlgebraSheafScalars.functor R X).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n)).obj.obj (op U) ≅
      (IntrinsicDeRham.SectionUnit.Intrinsic.sections R X U).X n :=
  (IntrinsicDeRham.SectionUnit.Intrinsic.evaluation R X U).mapIso (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X n)

theorem unit (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) n) :
    (iso R X U n).hom (FormSectionUnit.unit R X n U ω) =
      (IntrinsicDeRham.SectionUnit.Intrinsic.unit R X U).f n ω := by
  let P := GeometricComparison.Integral.FormsModules.IntegralFormsModules.presheaf R X n
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (AlgebraSheafificationScalars.map_fac R X P) (op U)) ω
  change ((AlgebraSheafificationScalars.objectIso R X P).hom.hom.app (op U))
    ((toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).app
      (op U) ω) = FormSectionUnit.unit R X n U ω at h
  rw [IntrinsicDeRham.SectionUnit.Intrinsic.unit_f]
  have hi : GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X n =
      (AlgebraSheafificationScalars.objectIso R X P).symm := by
    simp only [GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso,
      GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientPresheafIso, Functor.mapIso_refl, Iso.trans_refl]
    rfl
  unfold iso
  rw [hi]
  change ((AlgebraSheafificationScalars.objectIso R X P).inv.hom.app (op U))
    (FormSectionUnit.unit R X n U ω) = _
  rw [← h]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun a => a.hom) (AlgebraSheafificationScalars.objectIso R X P).hom_inv_id)
      (op U)) _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.IntrinsicFormNormalization.Intrinsic
