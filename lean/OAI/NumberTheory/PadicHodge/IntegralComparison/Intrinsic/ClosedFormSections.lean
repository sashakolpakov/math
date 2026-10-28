import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.FormTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleExactSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormSectionIso

/-! # Closed Form Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormSections

noncomputable section

/-! Top forms of the actual quotient algebra are the native sections
of the direct image of the differential-form sheaf. The map preserves
the ambient section-ring action, not only the base-ring action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsClosedImmersion f.left] (U : Y.left.Opens) (hU : IsAffineOpen U)

local instance ambientAlgebra : Algebra R Γ(Y.left, U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y U

abbrev quotient : CommAlgCat.{u} R :=
  CommAlgCat.of R (SmoothClosedSections.ring R Y U ⧸ f.left.ker.ideal ⟨U, hU⟩)

local instance formModule (n : ℕ) :
    Module Γ(Y.left, U) (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (quotient R X Y f U hU) n) :=
  inferInstanceAs (Module Γ(Y.left, U)
    (⋀[Γ(Y.left, U) ⧸ f.left.ker.ideal ⟨U, hU⟩]^n
      Ω[Γ(Y.left, U) ⧸ f.left.ker.ideal ⟨U, hU⟩⁄R]))

def quotientIso : quotient R X Y f U hU ≅ SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U) :=
  CommAlgCat.isoMk (SmoothClosedSections.quotientEquiv R X Y f U hU)

abbrev directImage (n : ℕ) :=
  (Scheme.Modules.pushforward f.left).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n)

variable (σ : Type u) [LinearOrder σ]
  [Algebra (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]

local instance closedAlgebra : Algebra Γ(Y.left, U) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)) :=
  (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sectionPullback f U).toRingHom.toAlgebra

local instance sectionModule (n : ℕ) : Module (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
    ((Affine.ModuleExactSections.sections U).obj (directImage R X Y f n)) :=
  inferInstanceAs (Module Γ(X.left, f.left ⁻¹ᵁ U)
    Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, f.left ⁻¹ᵁ U))

local instance sectionTower (n : ℕ) : IsScalarTower Γ(Y.left, U) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
    ((Affine.ModuleExactSections.sections U).obj (directImage R X Y f n)) where
  smul_assoc a b x := by
    change (algebraMap Γ(Y.left, U) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)) a * b) • x =
      algebraMap Γ(Y.left, U) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)) a • (b • x)
    exact mul_smul _ _ _

def iso (n : ℕ) :
    ModuleCat.of Γ(Y.left, U) (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (quotient R X Y f U hU) n) ≅
      (Affine.ModuleExactSections.sections U).obj (directImage R X Y f n) :=
  (Quotient.FormSectionIso.iso R Γ(Y.left, U) (f.left.ker.ideal ⟨U, hU⟩)
    (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)) ((Affine.ModuleExactSections.sections U).obj (directImage R X Y f n))
    (SmoothClosedSections.quotientEquiv R X Y f U hU) (fun _ => rfl) n
    (IntegralComparison.Etale.FormSections.Integral.exteriorIso R X (f.left ⁻¹ᵁ U) (hU.preimage f.left) σ n)).toModuleIso

theorem iso_apply (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (quotient R X Y f U hU) n) :
    (iso R X Y f U hU σ n).hom ω =
      (IntegralComparison.Etale.FormSections.Integral.exteriorIso R X (f.left ⁻¹ᵁ U) (hU.preimage f.left) σ n).symm
        (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (quotientIso R X Y f U hU).hom n ω) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormSections
