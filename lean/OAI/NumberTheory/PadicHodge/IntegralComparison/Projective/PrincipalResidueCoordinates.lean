import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.QuotientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterAdjunction

/-! # Principal Residue Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PrincipalResidueCoordinates

noncomputable section

/-! The actual projective negative resolution has the same principal
residue coefficient as the original parameter adjunction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.QuotientCoordinates.LocalAdjunction
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
  (b : Module.Basis (Fin (c + g)) Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) Ω[Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)⁄R])

local notation "N" => OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (c + g + 1)

def scalarFrame : Γ(N, U) ≃ₗ[Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)] Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) :=
  Affine.LineFrameNormalization.PrincipalOrientedResidue.sectionFrame U hU N
    (ParameterAdjunction.parameterFrame j U hU i hUi b)

def residueSections := by
  letI : (N).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (c + g + 1))
  letI (k : ℕ) : ((Affine.LinearResolutionPurity.internalComplex N (LocalAdjunction.source X f j B)).X k).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f.left j B (c + g + 1) hB k
  letI (k : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X k)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (LocalAdjunction.structureImage X f) j B k
  exact PrincipalResidue.SurvivorSection.sectionMap U hU N (scalarFrame j U hU i hUi b)
    (LocalAdjunction.source X f j B) f.left (NegativeResolution.augmentation (LocalAdjunction.structureImage X f) j B)
    s hs hreg

def residueMap := by
  letI : (N).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (c + g + 1))
  letI (k : ℕ) : ((Affine.LinearResolutionPurity.internalComplex N (LocalAdjunction.source X f j B)).X k).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f.left j B (c + g + 1) hB k
  letI (k : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X k)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (LocalAdjunction.structureImage X f) j B k
  exact PrincipalResidue.SurvivorData.map U hU N (scalarFrame j U hU i hUi b)
    (LocalAdjunction.source X f j B) f.left (NegativeResolution.augmentation (LocalAdjunction.structureImage X f) j B)
    s hs hreg

omit [Smooth X.hom] in
theorem residueSections_eq : residueSections X f j B hB U hU i hUi s hs hreg b =
    ParameterAdjunction.coefficient X f j B hB U hU i hUi s hs hreg b ≫
      (Closed.QuotientSectionNormalization.iso f.left U hU).inv := by
  let : (N).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (c + g + 1))
  let (k : ℕ) : ((Affine.LinearResolutionPurity.internalComplex N (LocalAdjunction.source X f j B)).X k).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f.left j B (c + g + 1) hB k
  let (k : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X k)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (LocalAdjunction.structureImage X f) j B k
  have h := PrincipalResidue.SectionCoordinates.Survivor.sectionMap_frame U hU N (LocalAdjunction.source X f j B) f.left
    (NegativeResolution.augmentation (LocalAdjunction.structureImage X f) j B) s hs hreg
    (ParameterAdjunction.parameterFrame j U hU i hUi b)
  rw [← QuotientCoordinates.LocalAdjunction.quotientSectionIso_eq_chart X f U hU] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PrincipalResidueCoordinates
