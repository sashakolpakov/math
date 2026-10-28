import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ParameterAdjunctionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterAmbientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormSymbols

/-! # Parameter Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterAdjunction

noncomputable section

/-! The original local projective adjunction evaluated in the prescribed
parameter frame. Its coefficient is the original oriented affine purity
map for the same negative-twist resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.MvPolynomial _root_.Module

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  ParameterNeighborhood.sectionAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R (c + g))
  [IsClosedImmersion f.left] [Smooth X.hom]
  (j : Fin (c + g + 1)) (B : ℕ) (hB : c + g + 1 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space R (c + g)).Opens) (hU : IsAffineOpen U)
  (i : Fin (c + g + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (s : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) s = LocalAdjunction.ideal X f U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) (List.ofFn s))
  (bI : Basis (Fin c) (LocalAdjunction.quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent)
  (hI : ∀ q, bI q = (LocalAdjunction.ideal X f U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)
      (LocalAdjunction.ideal X f U hU) s hs q))
  (bQ : Basis (Fin g) (LocalAdjunction.quotient X f U hU) Ω[LocalAdjunction.quotient X f U hU⁄R])
  (t : Fin g → Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U))
  (ht : ∀ q, bQ q = KaehlerDifferential.D R (LocalAdjunction.quotient X f U hU)
    (Ideal.Quotient.mk (LocalAdjunction.ideal X f U hU) (t q)))
  (b : Basis (Fin (c + g)) Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) Ω[Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)⁄R])
  (hb : (b : Fin (c + g) → Ω[Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)⁄R]) =
    Fin.append (fun q => KaehlerDifferential.D R Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) (s q))
      (fun q => KaehlerDifferential.D R Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) (t q)))

abbrev parameterFrame := ParameterLineAdjunction.frame b
  ((AffineOpen.InternalHom.sections U hU).obj
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (c + g + 1)))
  (AmbientAdjunction.chartLineExterior i U hU hUi j)

def coefficient :
    (Affine.ModuleExactSections.sections U).obj ((LocalAdjunction.dual X f j B).homology c) ⟶
      ModuleCat.of Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) (LocalAdjunction.quotient X f U hU) := by
  let (q : ℕ) : ((Affine.LinearResolutionPurity.internalComplex
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (c + g + 1)) (LocalAdjunction.source X f j B)).X q).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f.left j B (c + g + 1) hB q
  let (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X q)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (LocalAdjunction.structureImage X f) j B q
  exact (Affine.OrientedPurity.iso U hU
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (c + g + 1)) (LocalAdjunction.source X f j B)
    (LocalAdjunction.structureImage X f) (NegativeResolution.augmentation (LocalAdjunction.structureImage X f) j B)
    (LocalAdjunction.ideal X f U hU) (LocalAdjunction.quotientSectionIso X f U hU) s hs hreg
    (parameterFrame j U hU i hUi b)).hom

variable (τ : Type u) [LinearOrder τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]

def targetMap :
    ModuleCat.of Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) (⋀[LocalAdjunction.quotient X f U hU]^g Ω[LocalAdjunction.quotient X f U hU⁄R]) ⟶
    (Affine.ModuleExactSections.sections U).obj
      (Intrinsic.ClosedFormSections.directImage R X (IntrinsicOverlap.Intrinsic.model R (c + g)) f g) :=
  (Intrinsic.ClosedFormSections.iso R X (IntrinsicOverlap.Intrinsic.model R (c + g)) f U hU τ g).hom

abbrev affine_symbol (x : (Affine.ModuleExactSections.sections U).obj ((LocalAdjunction.dual X f j B).homology c)) :=
  letI hterms : ∀ q, ((Affine.LinearResolutionPurity.internalComplex
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (c + g + 1)) (LocalAdjunction.source X f j B)).X q).IsQuasicoherent :=
    fun q => LocalDualLine.term_quasicoherent f.left j B (c + g + 1) hB q
  letI hprojective : ∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X q)) :=
    fun q => Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (LocalAdjunction.structureImage X f) j B q
  letI : Smooth (IntrinsicOverlap.Intrinsic.model R (c + g)).hom := SpaceSmooth.smooth
  letI : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) :=
    Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R (c + g)) U hU
  letI : Algebra.Smooth R (LocalAdjunction.quotient X f U hU) :=
    Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R (c + g)) f U hU
  let ha : LocalAdjunction.ambientIso X f j U hU i hUi (rfl : c + g = c + g) =
      ParameterLineAdjunction.ambient (LocalAdjunction.ideal X f U hU) b
        ((AffineOpen.InternalHom.sections U hU).obj
          (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (c + g + 1)))
        (AmbientAdjunction.chartLineExterior i U hU hUi j) := by
    calc
      _ = AmbientAdjunction.ambientIso i U hU hUi j (LocalAdjunction.ideal X f U hU) := by
        ext a
        rfl
      _ = _ := ParameterAmbientCoordinates.ambient_eq i U hU hUi j (LocalAdjunction.ideal X f U hU) b
  Affine.ParameterAdjunctionCoordinates.symbol_with_ambient U hU
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (c + g + 1)) (LocalAdjunction.source X f j B)
    (LocalAdjunction.structureImage X f) (NegativeResolution.augmentation (LocalAdjunction.structureImage X f) j B)
    (LocalAdjunction.ideal X f U hU) (LocalAdjunction.quotientSectionIso X f U hU)
    (ClosedImmersionPurity.targetTrivialization j (c + g + 1) U hU i hUi)
    s hs hreg bI hI bQ t ht b hb
    (AmbientAdjunction.chartLineExterior i U hU hUi j)
    (LocalAdjunction.ambientIso X f j U hU i hUi rfl) ha x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterAdjunction
