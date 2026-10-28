import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AdjunctionFrameEvaluation

/-! # Frame Adjunction Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FrameAdjunctionEvaluation

noncomputable section

/-! The original projective adjunction map can be evaluated in any
frame of its ambient dualizing line, including a restricted frame. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Affine.OrientedPurity.iso
  Affine.DualizingAdjunction.iso Intrinsic.ClosedFormSections.iso
  ConormalAdjunction.equivalence LineValuedKoszulPurity.lineFrame

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (i : Fin (n + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

local instance frameAmbientAlgebra : Algebra R Γ(IntrinsicOverlap.Intrinsic.space R n, U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (IntrinsicOverlap.Intrinsic.model R n) U

local instance frameAmbientSmooth : Smooth (IntrinsicOverlap.Intrinsic.model R n).hom := SpaceSmooth.smooth

variable {c : ℕ} (s : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R n, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U) s = LocalAdjunction.ideal X f U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R n, U) (List.ofFn s))
  (eN : (AffineOpen.InternalHom.sections U hU).obj
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) ≅
      ModuleCat.of Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(IntrinsicOverlap.Intrinsic.space R n, U))

def orientedIsoInFrame := by
  let (q : ℕ) : ((Affine.LinearResolutionPurity.internalComplex
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) (LocalAdjunction.source X f j B)).X q).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f.left j B (n + 1) hB q
  let (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X q)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (LocalAdjunction.structureImage X f) j B q
  exact Affine.OrientedPurity.iso U hU
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) (LocalAdjunction.source X f j B)
    (LocalAdjunction.structureImage X f) (NegativeResolution.augmentation (LocalAdjunction.structureImage X f) j B)
    (LocalAdjunction.ideal X f U hU) (LocalAdjunction.quotientSectionIso X f U hU) s hs hreg eN

variable {g : ℕ} (hc : c + g = n)
  (bI : Module.Basis (Fin c) (LocalAdjunction.quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent)
  (bQ : Module.Basis (Fin g) (LocalAdjunction.quotient X f U hU) Ω[LocalAdjunction.quotient X f U hU⁄R])
  (τ : Type u) [LinearOrder τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]

theorem sectionIso_apply_frame
    (x : (Affine.ModuleExactSections.sections U).obj ((LocalAdjunction.dual X f j B).homology c)) :
    letI : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, U) := Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) U hU
    letI : Algebra.Smooth R (LocalAdjunction.quotient X f U hU) := Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f U hU
    (LocalAdjunction.sectionIso X f j B hB U hU i hUi hc s hs hreg bI bQ τ).hom x =
      (Intrinsic.ClosedFormSections.iso R X (IntrinsicOverlap.Intrinsic.model R n) f U hU τ g).hom
        (ConormalAdjunction.equivalence (k := R) (R := Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (LocalAdjunction.ideal X f U hU) bI bQ
          (LocalAdjunction.ambientIso X f j U hU i hUi hc
            ((LineValuedKoszulPurity.lineFrame Γ(IntrinsicOverlap.Intrinsic.space R n, U) (LocalAdjunction.ideal X f U hU)
              ((AffineOpen.InternalHom.sections U hU).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))) eN).symm
                ((orientedIsoInFrame X f j B hB U hU i hUi s hs hreg eN).hom x)))) := by
  let : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, U) := Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) U hU
  let : Algebra.Smooth R (LocalAdjunction.quotient X f U hU) := Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f U hU
  let (q : ℕ) : ((Affine.LinearResolutionPurity.internalComplex
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) (LocalAdjunction.source X f j B)).X q).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f.left j B (n + 1) hB q
  let (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X q)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (LocalAdjunction.structureImage X f) j B q
  have h := Affine.AdjunctionFrameEvaluation.adjunction_apply_with_frame (k := R) U hU
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) (LocalAdjunction.source X f j B)
    (LocalAdjunction.structureImage X f) (NegativeResolution.augmentation (LocalAdjunction.structureImage X f) j B)
    (LocalAdjunction.ideal X f U hU) (LocalAdjunction.quotientSectionIso X f U hU)
    (ClosedImmersionPurity.targetTrivialization j (n + 1) U hU i hUi) eN
    s hs hreg bI bQ (LocalAdjunction.ambientIso X f j U hU i hUi hc) x
  exact congrArg (fun y => (Intrinsic.ClosedFormSections.iso R X (IntrinsicOverlap.Intrinsic.model R n) f U hU τ g).hom y) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FrameAdjunctionEvaluation
