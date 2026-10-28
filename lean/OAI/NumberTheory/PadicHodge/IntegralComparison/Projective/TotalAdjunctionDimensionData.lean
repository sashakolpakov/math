import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueTotalAdjunction

/-! # Total Adjunction Dimension Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalAdjunctionDimensionData.Residue

noncomputable section

/-! Transport the original residue comparison across the equality
between the ambient dimension and codimension plus relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module _root_.HomologicalComplex Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g N : ℕ} (h : c + g = N)
attribute [local instance] MvPolynomial.gradedAlgebra
  LocalAdjunction.ambientAlgebra ParameterChart.coordinateOrder
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (j : Fin (N + 1)) (B : ℕ) (hB : N + 1 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)
  (i : Fin (N + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (s : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R N, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R N, U) s = LocalAdjunction.ideal X f U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R N, U) (List.ofFn s))
  (bI : Basis (Fin c) (LocalAdjunction.quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent)
  (hI : ∀ k, bI k = (LocalAdjunction.ideal X f U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(IntrinsicOverlap.Intrinsic.space R N, U) (LocalAdjunction.ideal X f U hU) s hs k))
  (bQ : Basis (Fin g) (LocalAdjunction.quotient X f U hU) Ω[LocalAdjunction.quotient X f U hU⁄R])
  (t : Fin g → Γ(IntrinsicOverlap.Intrinsic.space R N, U))
  (ht : ∀ k, bQ k = KaehlerDifferential.D R (LocalAdjunction.quotient X f U hU)
    (Ideal.Quotient.mk (LocalAdjunction.ideal X f U hU) (t k)))
  (b : Basis (Fin N) Γ(IntrinsicOverlap.Intrinsic.space R N, U) Ω[Γ(IntrinsicOverlap.Intrinsic.space R N, U)⁄R])
  (hb : (fun k : Fin (c + g) => b (Fin.cast h k)) =
    Fin.append (fun k => KaehlerDifferential.D R Γ(IntrinsicOverlap.Intrinsic.space R N, U) (s k))
      (fun k => KaehlerDifferential.D R Γ(IntrinsicOverlap.Intrinsic.space R N, U) (t k)))
  (τ : Type u) [Fintype τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]

local notation "L" => OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (N + 1)

include h hB in
omit [Smooth X.hom] [IsProper X.hom] in
theorem exactAt (a : ℕ) (ha : a ≠ c) : (LocalAdjunction.dual X f j B).ExactAt a := by
  let : SmoothOfRelativeDimension g (f.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
    change SmoothOfRelativeDimension g (f.left ≫ (IntrinsicOverlap.Intrinsic.model R N).hom)
    rw [Over.w f]
    infer_instance
  apply SmoothDualPurity.exactAt f.left j B (N+1) hB g a
  simp only [Fintype.card_fin, Nat.add_sub_cancel_right]
  have hc : N - g = c := by omega
  simpa only [hc] using ha

variable {ι : Type u} [LinearOrder ι]
  (W : ι → Principal.SectionPresheaf.Index U) (q : ℕ)

def residue := by
  letI : (L).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (N+1))
  letI (k : ℕ) : ((LocalAdjunction.source X f j B).X k).IsQuasicoherent :=
    ClosedImmersionPurity.source_quasicoherent f.left j B k
  letI (k : ℕ) : ((Affine.LinearResolutionPurity.internalComplex L (LocalAdjunction.source X f j B)).X k).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f.left j B (N+1) hB k
  letI (k : ℕ) : CategoryTheory.Projective ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X k)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (LocalAdjunction.structureImage X f) j B k
  letI : QuasiIso (NegativeResolution.augmentation (LocalAdjunction.structureImage X f) j B) :=
    inferInstanceAs (QuasiIso (NegativeResolution.tower (LocalAdjunction.structureImage X f) j B).augmentation)
  exact Principal.OrientedResidue.map f.left U hU L
    (PrincipalResidueCoordinates.scalarFrame (c := N) (g := 0) j U hU i hUi b) (LocalAdjunction.source X f j B)
    (NegativeResolution.augmentation (LocalAdjunction.structureImage X f) j B) s hs hreg

def symbol :=
  (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(IntrinsicOverlap.Intrinsic.space R N, U)) (.up ℕ) c).map
    (Principal.DifferentialSymbol.map R X (IntrinsicOverlap.Intrinsic.model R N) f U hU g (fun k => f.left.app U (t k)))

def concentration := by
  letI (k : ℕ) : ((Affine.LinearResolutionPurity.internalComplex L (LocalAdjunction.source X f j B)).X k).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f.left j B (N+1) hB k
  exact PrincipalReference.Concentration.Reference.iso U hU W
    (Affine.LinearResolutionPurity.internalComplex L (LocalAdjunction.source X f j B)) c (exactAt h X f j B hB) q

def adjunction :=
  (PrincipalReference.Concentration.Reference.functor U hU W q).map
    ((single (IntrinsicOverlap.Intrinsic.space R N).Modules (.up ℕ) c).map
      (ParameterGlobalCoordinates.iso X f (by omega : c = N-g)
        j B hB (by omega : g ≤ N)).hom)

def coefficient :=
  (singleMapHomologicalComplex (Principal.ModuleFunctor.functor U hU) (.up ℕ) c).hom.app
    ((Scheme.Modules.pushforward f.left).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g))

def leftMap :=
  (Supported.CechHomotopyEquivalence.functor W q).map
      (residue X f j B U hU i hUi s hs hreg b) ≫
    (Supported.CechHomotopyEquivalence.functor W q).map (symbol X f U hU t)

def rightMap :=
  (concentration h X f j B hB U hU W q).hom ≫ adjunction h X f j B hB U hU W q ≫
    (Supported.CechHomotopyEquivalence.functor W q).map (coefficient (c := c) (g := g) X f U hU)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalAdjunctionDimensionData.Residue
