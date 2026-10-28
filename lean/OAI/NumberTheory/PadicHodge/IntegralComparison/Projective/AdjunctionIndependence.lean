import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AdjunctionIndependence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormRestriction

/-! # Adjunction Independence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionIndependence

noncomputable section

/-! The native local adjunction isomorphism is independent of every
chosen projective chart, regular equation, and differential coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (i k : Fin (n + 1))
  (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)

local instance ambientAlgebra : Algebra R Γ(IntrinsicOverlap.Intrinsic.space R n, U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (IntrinsicOverlap.Intrinsic.model R n) U

variable {c g : ℕ} (hc : c + g = n)

omit [IsNoetherianRing R] [IsClosedImmersion f.left] [Smooth X.hom] in
theorem ambient_independent :
    LocalAdjunction.ambientIso X f j U hU i hUi hc = LocalAdjunction.ambientIso X f j U hU k hUk hc := by
  exact congrArg (fun e => LinearEquiv.trans e
      (eqToIso (congrArg (fun d => ModuleCat.of (LocalAdjunction.quotient X f U hU)
        (⋀[LocalAdjunction.quotient X f U hU]^d
          ((LocalAdjunction.quotient X f U hU) ⊗[Γ(IntrinsicOverlap.Intrinsic.space R n, U)] Ω[Γ(IntrinsicOverlap.Intrinsic.space R n, U)⁄R]))) hc.symm)).toLinearEquiv)
    (AmbientNormalization.Adjunction.ambientIso_independent_chart i U hU hUi k hUk j (LocalAdjunction.ideal X f U hU))

variable (s : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R n, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U) s = LocalAdjunction.ideal X f U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R n, U) (List.ofFn s))
  (bI : Module.Basis (Fin c) (LocalAdjunction.quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent)
  (hbI : ∀ a, bI a = (LocalAdjunction.ideal X f U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(IntrinsicOverlap.Intrinsic.space R n, U) (LocalAdjunction.ideal X f U hU) s hs a))
  (t : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R n, U))
  (ht : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U) t = LocalAdjunction.ideal X f U hU)
  (htreg : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R n, U) (List.ofFn t))
  (bt : Module.Basis (Fin c) (LocalAdjunction.quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent)
  (hbt : ∀ a, bt a = (LocalAdjunction.ideal X f U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(IntrinsicOverlap.Intrinsic.space R n, U) (LocalAdjunction.ideal X f U hU) t ht a))
  (bQ bQ' : Module.Basis (Fin g) (LocalAdjunction.quotient X f U hU) Ω[LocalAdjunction.quotient X f U hU⁄R])
  (τ : Type u) [LinearOrder τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  (τ' : Type u) [LinearOrder τ']
  [Algebra (MvPolynomial τ' R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ' R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ' R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]

include hbI hbt in
theorem same_open :
    LocalAdjunction.sectionIso X f j B hB U hU i hUi hc s hs hreg bI bQ τ =
      LocalAdjunction.sectionIso X f j B hB U hU k hUk hc t ht htreg bt bQ' τ' := by
  let (q : ℕ) : ((Affine.LinearResolutionPurity.internalComplex
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) (LocalAdjunction.source X f j B)).X q).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f.left j B (n + 1) hB q
  let (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X q)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (LocalAdjunction.structureImage X f) j B q
  let : Smooth (IntrinsicOverlap.Intrinsic.model R n).hom := SpaceSmooth.smooth
  let : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, U) := Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) U hU
  let : Algebra.Smooth R (LocalAdjunction.quotient X f U hU) := Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f U hU
  exact congrArg₂ (fun e₁ e₂ => e₁ ≪≫ e₂)
    (Affine.AdjunctionIndependence.independent U hU
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) (LocalAdjunction.source X f j B)
      (LocalAdjunction.structureImage X f) (NegativeResolution.augmentation (LocalAdjunction.structureImage X f) j B)
      (LocalAdjunction.ideal X f U hU) (LocalAdjunction.quotientSectionIso X f U hU)
      (ClosedImmersionPurity.targetTrivialization j (n + 1) U hU i hUi)
      (ClosedImmersionPurity.targetTrivialization j (n + 1) U hU k hUk)
      s hs hreg bI hbI t ht htreg bt hbt bQ bQ'
      (LocalAdjunction.ambientIso X f j U hU i hUi hc) (LocalAdjunction.ambientIso X f j U hU k hUk hc)
      (ambient_independent X f j U hU i k hUi hUk hc))
    (Intrinsic.ClosedFormRestriction.coordinate_independent R X (IntrinsicOverlap.Intrinsic.model R n) f U hU τ τ' g)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionIndependence
