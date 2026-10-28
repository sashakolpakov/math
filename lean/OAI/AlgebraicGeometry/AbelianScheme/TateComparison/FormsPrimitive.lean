import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ProjectiveFormFaithfulness
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PrimitiveFormTrace
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiEndAdditivity
import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed

/-! # Forms Primitive -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormsPrimitive

noncomputable section

/-! Every actual algebraic one-form on a complex abelian variety is primitive. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem abelian_formsPullback_mul (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f g : V.toOver ⟶ A.toOver) (form : FormConstants.OneForms A.toOver) :
    FormConstants.formsPullback (f * g) form = FormConstants.formsPullback f form + FormConstants.formsPullback g form := by
  apply ProjectiveFormFaithfulness.kaehlerBettiClass_injective V
  rw [map_add, HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass_pullback, HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass_pullback,
    HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass_pullback]
  exact HodgeConjecture.HeckeCycles.BettiEndAdditivity.CM.complex_pullback_mul A f g _

theorem abelian_oneForm_primitive (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (form : FormConstants.OneForms A.toOver) :
    PrimitiveFormTrace.IsPrimitiveOneForm form := by
  let V := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety A.variety A.variety
  let f : V.toOver ⟶ A.toOver := fst A.toOver A.toOver
  let g : V.toOver ⟶ A.toOver := snd A.toOver A.toOver
  have h := abelian_formsPullback_mul A V f g form
  intro R x y
  have hv := congrArg (fun w : FormConstants.OneForms V.toOver => w.val R (lift x y)) h
  change form.val R (lift x y ≫ (f * g)) =
    form.val R (lift x y ≫ f) + form.val R (lift x y ≫ g) at hv
  have hf : lift x y ≫ f = x := lift_fst x y
  have hg : lift x y ≫ g = y := lift_snd x y
  have hm : lift x y ≫ (f * g) = x * y :=
    (MonObj.comp_mul (lift x y) f g).trans (congrArg₂ (· * ·) hf hg)
  exact (congrArg (form.val R) hm).symm.trans
    (hv.trans (congrArg₂ (· + ·) (congrArg (form.val R) hf) (congrArg (form.val R) hg)))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormsPrimitive
