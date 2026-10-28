import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.DualizingAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalDualLine
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.FormCoherence

/-! # Local Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction

noncomputable section

/-! Local adjunction identifies the surviving cohomology of the
original projective dual resolution with the actual top-form sheaf
of the smooth closed subscheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (i : Fin (n + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

local instance ambientAlgebra : Algebra R Γ(IntrinsicOverlap.Intrinsic.space R n, U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (IntrinsicOverlap.Intrinsic.model R n) U

abbrev ideal := f.left.ker.ideal ⟨U, hU⟩
abbrev quotient := Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ LocalAdjunction.ideal X f U hU
abbrev structureImage := ClosedImmersionPurity.directImage f.left
abbrev source := ClosedImmersionPurity.source f.left j B
abbrev dual := ClosedImmersionPurity.internalComplex f.left j B (n + 1)

def quotientSectionIso :
    (AffineOpen.InternalHom.sections U hU).obj (structureImage X f) ≅
      ModuleCat.of Γ(IntrinsicOverlap.Intrinsic.space R n, U) (quotient X f U hU) :=
  (Affine.ChartSections.iso U hU (structureImage X f)).symm ≪≫
    (Closed.ImmersionQuotientSections.quotientIso f.left U hU).symm ≪≫
      eqToIso (congrArg (fun I : Ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U) => ModuleCat.of Γ(IntrinsicOverlap.Intrinsic.space R n, U) (Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I))
        (f.left.ker_apply ⟨U, hU⟩).symm)

variable {c g : ℕ} (hc : c + g = n)
  (s : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R n, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U) s = LocalAdjunction.ideal X f U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R n, U) (List.ofFn s))
  (bI : Module.Basis (Fin c) (quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent)
  (bQ : Module.Basis (Fin g) (quotient X f U hU) Ω[quotient X f U hU⁄R])

def ambientIso :
    (quotient X f U hU) ⊗[Γ(IntrinsicOverlap.Intrinsic.space R n, U)]
      (AffineOpen.InternalHom.sections U hU).obj
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) ≃ₗ[quotient X f U hU]
      ⋀[quotient X f U hU]^(c + g)
        ((quotient X f U hU) ⊗[Γ(IntrinsicOverlap.Intrinsic.space R n, U)] Ω[Γ(IntrinsicOverlap.Intrinsic.space R n, U)⁄R]) :=
  (AmbientAdjunction.ambientIso i U hU hUi j (LocalAdjunction.ideal X f U hU)).trans
    (eqToIso (congrArg (fun d => ModuleCat.of (quotient X f U hU)
      (⋀[quotient X f U hU]^d
        ((quotient X f U hU) ⊗[Γ(IntrinsicOverlap.Intrinsic.space R n, U)] Ω[Γ(IntrinsicOverlap.Intrinsic.space R n, U)⁄R]))) hc.symm)).toLinearEquiv

variable (τ : Type u) [LinearOrder τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]

def sectionIso :
    (Affine.ModuleExactSections.sections U).obj ((dual X f j B).homology c) ≅
      (Affine.ModuleExactSections.sections U).obj
        (Intrinsic.ClosedFormSections.directImage R X (IntrinsicOverlap.Intrinsic.model R n) f g) := by
  let (q : ℕ) : ((Affine.LinearResolutionPurity.internalComplex
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) (source X f j B)).X q).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f.left j B (n + 1) hB q
  let (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((source X f j B).X q)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (structureImage X f) j B q
  let : Smooth (IntrinsicOverlap.Intrinsic.model R n).hom := SpaceSmooth.smooth
  let : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, U) := Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) U hU
  let : Algebra.Smooth R (quotient X f U hU) := Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f U hU
  exact Affine.DualizingAdjunction.iso U hU
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) (source X f j B)
    (structureImage X f) (NegativeResolution.augmentation (structureImage X f) j B)
    (LocalAdjunction.ideal X f U hU) (quotientSectionIso X f U hU)
    (ClosedImmersionPurity.targetTrivialization j (n + 1) U hU i hUi)
    s hs hreg bI bQ (ambientIso X f j U hU i hUi hc) ≪≫
      Intrinsic.ClosedFormSections.iso R X (IntrinsicOverlap.Intrinsic.model R n) f U hU τ g

variable [IsProper X.hom]

def openIso : ((dual X f j B).homology c).restrict U.ι ≅
    (Intrinsic.ClosedFormSections.directImage R X (IntrinsicOverlap.Intrinsic.model R n) f g).restrict U.ι := by
  let := LocalDualLine.homology_quasicoherent f.left j B (n + 1) hB c
  let := IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R X g
  let := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f.left
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
  exact AffineSection.Isomorphism.openIso U hU _ _
    (sectionIso X f j B hB U hU i hUi hc s hs hreg bI bQ τ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction
