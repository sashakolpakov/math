import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.IntrinsicFormNormalization

/-! # Intrinsic Form Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.IntrinsicFormRestriction.Intrinsic

noncomputable section

/-! The native form comparison preserves literal sheaf restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (n : ℕ) {U V : X.left.Opens} (i : V ⟶ U)

theorem restriction (z : Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, U)) :
    (IntrinsicFormNormalization.Intrinsic.iso R X V n).hom
      ((GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n).presheaf.map i.op z) =
    ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n).obj.map i.op
      ((IntrinsicFormNormalization.Intrinsic.iso R X U n).hom z) :=
  ConcreteCategory.congr_hom
    ((GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X n).hom.hom.naturality i.op) z

theorem restriction_smul (b : Γ(X.left, U))
    (z : Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, U)) :
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n).presheaf.map i.op (b • z) =
      X.left.presheaf.map i.op b •
        (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n).presheaf.map i.op z :=
  ((GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n).val.map i.op).hom.map_smulₛₗ b z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.IntrinsicFormRestriction.Intrinsic
