import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormDualTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.IntrinsicFormNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.DeRhamSheafTraceNormalization

/-! # Etale Form Duality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormDuality

noncomputable section

/-! Actual source module-form sections are the coefficient dual of
actual target module-form sections. Evaluation at one agrees with the
original global finite étale de Rham trace through its native comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] (U : Y.left.Opens) [Fact (IsAffineOpen U)]

local instance : Algebra (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.sectionAlgebra R X Y f U
local instance : IsScalarTower R (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.sectionTower R X Y f U
local instance : Algebra.Etale (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.sectionEtale R X Y f U Fact.out

variable (σ : Type u) [Fintype σ] [LinearOrder σ]
  [Algebra (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)]
  [IsScalarTower R (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)]
  [Algebra.Etale (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)]

local instance : Algebra (MvPolynomial σ R) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.polynomialSource R X Y f U σ
local instance : IsScalarTower (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.polynomialTower R X Y f U σ
local instance : IsScalarTower R (MvPolynomial σ R) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.polynomialBaseTower R X Y f U σ
local instance : Algebra.Etale (MvPolynomial σ R) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.sourceEtale R X Y f U σ

abbrev sourceSections (n : ℕ) := Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, f.left ⁻¹ᵁ U)
abbrev targetSections (n : ℕ) := Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y n, U)

local instance sourceScalar (n : ℕ) : Module (AffineOpen.DeRhamTrace.sourceRing R X Y f U) (sourceSections R X Y f U n) :=
  inferInstanceAs (Module Γ(X.left, f.left ⁻¹ᵁ U) (sourceSections R X Y f U n))
local instance targetScalar (n : ℕ) : Module (AffineOpen.DeRhamTrace.targetRing R Y U) (targetSections R Y U n) :=
  inferInstanceAs (Module Γ(Y.left, U) (targetSections R Y U n))
local instance restrictedScalar (n : ℕ) : Module (AffineOpen.DeRhamTrace.targetRing R Y U) (sourceSections R X Y f U n) :=
  Module.compHom (sourceSections R X Y f U n) (algebraMap (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U))
local instance (n : ℕ) : IsScalarTower (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U)
    (sourceSections R X Y f U n) := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

variable [Module.Free (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U)]
  [Module.Finite (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U)]

def equiv (n : ℕ) : sourceSections R X Y f U n ≃ₗ[AffineOpen.DeRhamTrace.targetRing R Y U]
    (AffineOpen.DeRhamTrace.sourceRing R X Y f U →ₗ[AffineOpen.DeRhamTrace.targetRing R Y U] targetSections R Y U n) :=
  ((IntegralComparison.Etale.FormSections.Integral.unitIso R X (f.left ⁻¹ᵁ U)
      ((Fact.out : IsAffineOpen U).preimage f.left) σ n).symm.restrictScalars (AffineOpen.DeRhamTrace.targetRing R Y U)).trans
    ((IntegralComparison.Etale.FormDualTrace.equiv R (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) σ n).trans
      (LinearEquiv.congrRight (IntegralComparison.Etale.FormSections.Integral.unitIso R Y U Fact.out σ n)))

omit [Fintype σ] in
theorem equiv_unit (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (AffineOpen.DeRhamTrace.sourceRing R X Y f U) n)
    (b : AffineOpen.DeRhamTrace.sourceRing R X Y f U) :
    equiv R X Y f U σ n (Integral.FormSectionUnit.unit R X n (f.left ⁻¹ᵁ U) ω) b =
      Integral.FormSectionUnit.unit R Y n U
        (IntegralComparison.Etale.FormDualTrace.equiv R (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) σ n ω b) := by
  change Integral.FormSectionUnit.unit R Y n U
    (IntegralComparison.Etale.FormDualTrace.equiv R (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) σ n
      ((IntegralComparison.Etale.FormSections.Integral.unitIso R X (f.left ⁻¹ᵁ U)
        ((Fact.out : IsAffineOpen U).preimage f.left) σ n).symm
        ((IntegralComparison.Etale.FormSections.Integral.unitIso R X (f.left ⁻¹ᵁ U)
          ((Fact.out : IsAffineOpen U).preimage f.left) σ n) ω)) b) = _
  rw [LinearEquiv.symm_apply_apply]

variable {ι : Type v} [Fintype ι]
  (b : Module.Basis ι (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U))

theorem native_trace (n : ℕ) (z : sourceSections R X Y f U n) :
    (Integral.IntrinsicFormNormalization.Intrinsic.iso R Y U n).hom (equiv R X Y f U σ n z 1) =
      (AffineOpen.DeRhamTrace.map R X Y f U σ b).f n
        ((Integral.IntrinsicFormNormalization.Intrinsic.iso R X (f.left ⁻¹ᵁ U) n).hom z) := by
  obtain ⟨ω, rfl⟩ := IntegralComparison.Etale.FormSections.Integral.unit_bijective R X (f.left ⁻¹ᵁ U)
    ((Fact.out : IsAffineOpen U).preimage f.left) σ n |>.surjective z
  rw [equiv_unit, Integral.IntrinsicFormNormalization.Intrinsic.unit, Integral.IntrinsicFormNormalization.Intrinsic.unit]
  rw [← IntegralComparison.Etale.FormDualTrace.trace_eq_eval_one R (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) σ b]
  have h0 := congrArg (fun a => a.f n) (AffineOpen.DeRhamTrace.map_unit R X Y f U σ b)
  have h := ConcreteCategory.congr_hom (C := ModuleCat R) h0 ω
  exact h.symm

variable [IsProper Y.hom] [Smooth Y.hom]

include b in
theorem global_trace (n : ℕ) (z : sourceSections R X Y f U n) :
    (Integral.IntrinsicFormNormalization.Intrinsic.iso R Y U n).hom (equiv R X Y f U σ n z 1) =
      ((FiniteEtale.DeRhamSheafTrace.trace R X Y f).f n).hom.app (op U)
        ((Integral.IntrinsicFormNormalization.Intrinsic.iso R X (f.left ⁻¹ᵁ U) n).hom z) := by
  rw [FiniteEtale.DeRhamSheafTraceNormalization.trace_app_of_chart R X Y f U σ b]
  exact native_trace R X Y f U σ b n z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormDuality
