import OAI.RepresentationTheory.Theta.Geometric.CentralFormTrace
import OAI.RepresentationTheory.Theta.Geometric.Rational.FormComposition

/-! # Inverse Central Form Powers -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Inverting the actual central unit undoes the marking shift on
algebraic forms, with equality on every affine test. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem InverseCentralFormPowers.formsPullback_iso_cancel {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (e : X ≅ Y)
    (form : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms Y) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback e.inv (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback e.hom form) = form := by
  change ((AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback e.inv).comp (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback e.hom)) form = form
  rw [← AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, e.inv_hom_id, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_id]
  rfl

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)

include hA

theorem Data.ActiveHeckeThetaData.centralInverseForms_markingShift (u : D.pel.EndQˣ)
    (hu : (u : D.pel.EndQ) = A.algebraAction (A.basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s)))
    (form : D.pel.OneFormsA) :
    D.pel.albanesePullback hg (D.rationalFormsPullback hg (↑u⁻¹ : D.pel.EndQ) form) =
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.complexMarkingShift A).inv (D.pel.albanesePullback hg form) := by
  have hc := D.centralRationalForms_markingShift hg hgood hIsogenyQuotient A hA
    (D.rationalFormsPullback hg (↑u⁻¹ : D.pel.EndQ) form)
  change D.pel.albanesePullback hg
    (D.rationalFormsPullback hg (A.algebraAction (A.basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s)))
      (D.rationalFormsPullback hg (↑u⁻¹ : D.pel.EndQ) form)) = _ at hc
  have hcancel := congrArg (fun f : Module.End ℂ D.pel.OneFormsA => f form)
    (D.rationalUnitForms hg u).val_inv
  change D.rationalFormsPullback hg (u : D.pel.EndQ)
    (D.rationalFormsPullback hg (↑u⁻¹ : D.pel.EndQ) form) = form at hcancel
  rw [← hu, hcancel] at hc
  have hi := congrArg (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.complexMarkingShift A).inv) hc
  rw [InverseCentralFormPowers.formsPullback_iso_cancel] at hi
  exact hi.symm

end

/-! Repeated inverse central operators equal repeated inverse marking
pullbacks on the original algebraic one-forms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry)

theorem Data.ActiveHeckeThetaData.rationalFormsPullback_pow (a : D.pel.EndQ) (n : ℕ) :
    D.rationalFormsPullback hg (a ^ n) = D.rationalFormsPullback hg a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, D.rationalFormsPullback_one]
  | succ n ih =>
    rw [pow_succ, D.rationalFormsPullback_mul, ih, pow_succ']
    rfl

variable (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)

include hA

theorem Data.ActiveHeckeThetaData.centralInverseForms_power_markingShift (u : D.pel.EndQˣ)
    (hu : (u : D.pel.EndQ) = A.algebraAction (A.basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s)))
    (n : ℕ) (form : D.pel.OneFormsA) :
    D.pel.albanesePullback hg
      (D.rationalFormsPullback hg ((↑u⁻¹ : D.pel.EndQ) ^ n) form) =
      (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.complexMarkingShift A).inv)^[n]
        (D.pel.albanesePullback hg form) := by
  induction n with
  | zero =>
    rw [pow_zero, D.rationalFormsPullback_one, Function.iterate_zero]
    rfl
  | succ n ih =>
    rw [pow_succ, D.rationalFormsPullback_mul]
    change D.pel.albanesePullback hg
      (D.rationalFormsPullback hg (↑u⁻¹ : D.pel.EndQ)
        (D.rationalFormsPullback hg ((↑u⁻¹ : D.pel.EndQ) ^ n) form)) = _
    rw [D.centralInverseForms_markingShift hg hgood hIsogenyQuotient A hA u hu, ih,
      Function.iterate_succ_apply']

end

end OAI.RepresentationTheory.Theta.Geometric
