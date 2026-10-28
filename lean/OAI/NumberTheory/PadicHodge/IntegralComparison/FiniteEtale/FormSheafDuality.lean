import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasisRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomPrincipalExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisGluingNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.MapPureTrace

/-! # Form Sheaf Duality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FormSheafDuality

noncomputable section

/-! The original finite étale source form sheaf is the internal Hom
of its function sheaf into target forms. The glued isomorphism is
normalized by the original de Rham sheaf trace at the coefficient unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormRestriction

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left]

abbrev coefficients := (Scheme.Modules.pushforward f.left).obj (SheafOfModules.unit X.left.ringCatSheaf)
abbrev source (n : ℕ) := (Scheme.Modules.pushforward f.left).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n)
abbrev forms (n : ℕ) := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y n
abbrev target (n : ℕ) := ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (coefficients R X Y f) (forms R Y n)

local instance coefficient_qc : (coefficients R X Y f).IsQuasicoherent := by
  let : (SheafOfModules.unit X.left.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f.left

def sectionEquiv (a : TraceBasis.Index R X Y f) (n : ℕ) :
    Γ(source R X Y f n, a.val) ≃ₗ[Γ(Y.left, a.val)] Γ(target R X Y f n, a.val) := by
  let e : Γ(source R X Y f n, a.val) ≃ₗ[Γ(Y.left, a.val)]
      (Γ(coefficients R X Y f, a.val) →ₗ[Γ(Y.left, a.val)] Γ(forms R Y n, a.val)) :=
    Intrinsic.EtaleFormRestriction.localEquiv R X Y f a n
  exact e.trans
    (Affine.HomSectionsEquiv.equiv a.val a.property.1 (coefficients R X Y f) (forms R Y n)).symm

theorem sectionEquiv_evaluation (a : TraceBasis.Index R X Y f) (n : ℕ)
    (z : Γ(source R X Y f n, a.val)) (b : Γ(coefficients R X Y f, a.val)) :
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (coefficients R X Y f) (forms R Y n) a.val
      (sectionEquiv R X Y f a n z) b = Intrinsic.EtaleFormRestriction.localEquiv R X Y f a n z b := by
  change Affine.HomSectionsEquiv.equiv a.val a.property.1 (coefficients R X Y f) (forms R Y n)
    ((Affine.HomSectionsEquiv.equiv a.val a.property.1 (coefficients R X Y f) (forms R Y n)).symm
      (Intrinsic.EtaleFormRestriction.localEquiv R X Y f a n z)) b = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable [IsProper Y.hom] [Smooth Y.hom]

theorem principal (U : Y.left.Opens) (hU : IsAffineOpen U) (h : TraceBasis.Good R X Y f U)
    (r : Γ(Y.left, U)) (n : ℕ) (z : Γ(source R X Y f n, U)) :
    sectionEquiv R X Y f
      ⟨Y.left.basicOpen r, TraceBasisRestriction.good R X Y f U
        (Y.left.basicOpen r) h (hU.basicOpen r) (Y.left.basicOpen_le r)⟩ n
      ((source R X Y f n).presheaf.map (homOfLE (Y.left.basicOpen_le r)).op z) =
    (target R X Y f n).presheaf.map (homOfLE (Y.left.basicOpen_le r)).op
      (sectionEquiv R X Y f ⟨U, h⟩ n z) := by
  apply Affine.HomPrincipalExt.ext U hU r (coefficients R X Y f) (forms R Y n)
  intro b
  let a : TraceBasis.Index R X Y f := ⟨U, h⟩
  let a' : TraceBasis.Index R X Y f := ⟨Y.left.basicOpen r,
    TraceBasisRestriction.good R X Y f U (Y.left.basicOpen r) h
      (hU.basicOpen r) (Y.left.basicOpen_le r)⟩
  calc
    _ = Intrinsic.EtaleFormRestriction.localEquiv R X Y f a' n
        ((source R X Y f n).presheaf.map (homOfLE (Y.left.basicOpen_le r)).op z)
        ((coefficients R X Y f).presheaf.map (homOfLE (Y.left.basicOpen_le r)).op b) :=
      sectionEquiv_evaluation R X Y f a' n _ _
    _ = (forms R Y n).presheaf.map (homOfLE (Y.left.basicOpen_le r)).op
        (Intrinsic.EtaleFormRestriction.localEquiv R X Y f a n z b) :=
      (Intrinsic.EtaleFormRestriction.restriction R X Y f a a'
        (Y.left.basicOpen_le r) n z b).symm
    _ = _ := ((Affine.HomEvaluation.restriction (coefficients R X Y f) (forms R Y n) U
      (homOfLE (Y.left.basicOpen_le r)) (sectionEquiv R X Y f a n z) b).trans
        (congrArg ((forms R Y n).presheaf.map (homOfLE (Y.left.basicOpen_le r)).op)
          (sectionEquiv_evaluation R X Y f a n z b))).symm

def iso (n : ℕ) : source R X Y f n ≅ target R X Y f n :=
  Principal.BasisGluing.iso (source R X Y f n) (target R X Y f n) (TraceBasis.Good R X Y f)
    (fun U _ h => (sectionEquiv R X Y f ⟨U, h⟩ n).toLinearMap)
    (fun U hU h r => TraceBasisRestriction.good R X Y f U
      (Y.left.basicOpen r) h (hU.basicOpen r) (Y.left.basicOpen_le r))
    (fun U hU h r z => principal R X Y f U hU h r n z)
    (fun U x hx => by
      obtain ⟨a, hxa, haU⟩ := TraceBasis.neighborhood R X Y f U x hx
      exact ⟨a.val, a.property.1, a.property, hxa, haU⟩)
    (fun U _ h => (sectionEquiv R X Y f ⟨U, h⟩ n).bijective)

theorem iso_app (a : TraceBasis.Index R X Y f) (n : ℕ) (z : Γ(source R X Y f n, a.val)) :
    (iso R X Y f n).hom.app a.val z = sectionEquiv R X Y f a n z :=
  Principal.BasisGluingNormalization.iso_app (source R X Y f n) (target R X Y f n) (TraceBasis.Good R X Y f)
    (fun U _ h => (sectionEquiv R X Y f ⟨U, h⟩ n).toLinearMap)
    (fun U hU h r => TraceBasisRestriction.good R X Y f U
      (Y.left.basicOpen r) h (hU.basicOpen r) (Y.left.basicOpen_le r))
    (fun U hU h r z => principal R X Y f U hU h r n z)
    (fun U x hx => by
      obtain ⟨b, hxb, hbU⟩ := TraceBasis.neighborhood R X Y f U x hx
      exact ⟨b.val, b.property.1, b.property, hxb, hbU⟩)
    (fun U _ h => (sectionEquiv R X Y f ⟨U, h⟩ n).bijective) a.val a.property.1 a.property z

theorem trace (a : TraceBasis.Index R X Y f) (n : ℕ) (z : Γ(source R X Y f n, a.val)) :
    (Integral.IntrinsicFormNormalization.Intrinsic.iso R Y a.val n).hom
      (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (coefficients R X Y f) (forms R Y n) a.val
        ((iso R X Y f n).hom.app a.val z)
          (show Γ(coefficients R X Y f, a.val) from (1 : Γ(X.left, f.left ⁻¹ᵁ a.val)))) =
      ((DeRhamSheafTrace.trace R X Y f).f n).hom.app (op a.val)
        ((Integral.IntrinsicFormNormalization.Intrinsic.iso R X (f.left ⁻¹ᵁ a.val) n).hom z) := by
  rw [iso_app, sectionEquiv_evaluation]
  simpa only [one_smul] using Intrinsic.EtaleFormRestriction.evaluation R X Y f a n 1 z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FormSheafDuality
