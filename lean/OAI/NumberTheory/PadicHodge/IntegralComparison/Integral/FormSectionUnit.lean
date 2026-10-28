import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules

/-! # Form Section Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.FormSectionUnit

noncomputable section

/-! The original module sheafification unit is linear in local functions
and commutes with actual restriction of differential symbols. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (n : ℕ)

abbrev ring (U : X.left.Opens) := Γ(X.left, U)

local instance sectionAlgebra (U : X.left.Opens) : Algebra R (ring R X U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U

def unit (U : X.left.Opens) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (ring R X U) n →ₗ[ring R X U]
      Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, U) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.left.ringCatSheaf.obj)).unit.app
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.presheaf R X n)).app (op U)).hom

theorem restriction {U V : X.left.Opens} (i : V ⟶ U)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (ring R X U) n) :
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n).presheaf.map i.op (FormSectionUnit.unit R X n U ω) =
      FormSectionUnit.unit R X n V (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op) n ω) := by
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.left.ringCatSheaf.obj)).unit.app
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.presheaf R X n)) i.op ω).symm

theorem bijective (U : X.left.Opens)
    [IsIso ((toSheafify (Opens.grothendieckTopology X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).app (op U))] :
    Function.Bijective (FormSectionUnit.unit R X n U) := by
  let P := GeometricComparison.Integral.FormsModules.IntegralFormsModules.presheaf R X n
  let η := AlgebraSheafificationScalars.unit R X P
  have he := congrArg (fun f => f.app (op U))
    (AlgebraSheafificationScalars.map_fac R X P)
  have hη : IsIso (η.app (op U)) := by
    rw [← he]
    change IsIso ((toSheafify (Opens.grothendieckTopology X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).app (op U) ≫
      (AlgebraSheafificationScalars.map R X P).hom.app (op U))
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (η.app (op U))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.FormSectionUnit
