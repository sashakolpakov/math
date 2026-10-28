import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FormSheafDuality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.HomUnitEvaluation

/-! # Module Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ModuleTrace

noncomputable section

/-! The coefficient-dual evaluation is an actual structure-module
trace on source forms. On native affine charts it is the original
finite étale de Rham trace, with no scalar ambiguity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FormSheafDuality
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]

def trace (n : ℕ) : FormSheafDuality.source R X Y f n ⟶ FormSheafDuality.forms R Y n :=
  (FormSheafDuality.iso R X Y f n).hom ≫
    Sheaf.HomUnitEvaluation.map (FormSheafDuality.coefficients R X Y f) (FormSheafDuality.forms R Y n)
      (SheafOfModules.unitToPushforwardObjUnit f.left.toRingCatSheafHom)

theorem normalization (a : TraceBasis.Index R X Y f) (n : ℕ)
    (z : Γ(FormSheafDuality.source R X Y f n, a.val)) :
    (Integral.IntrinsicFormNormalization.Intrinsic.iso R Y a.val n).hom ((trace R X Y f n).app a.val z) =
      ((DeRhamSheafTrace.trace R X Y f).f n).hom.app (op a.val)
        ((Integral.IntrinsicFormNormalization.Intrinsic.iso R X (f.left ⁻¹ᵁ a.val) n).hom z) := by
  change (Integral.IntrinsicFormNormalization.Intrinsic.iso R Y a.val n).hom
    (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen _ _ a.val
      ((FormSheafDuality.iso R X Y f n).hom.app a.val z) ((f.left.app a.val).hom 1)) = _
  rw [map_one]
  exact FormSheafDuality.trace R X Y f a n z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ModuleTrace
