import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterGlobalSymbol
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PrincipalResidueCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.DifferentialSymbol

/-! # Residue Local Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueLocalAdjunction

noncomputable section

/-! The original global projective adjunction on an affine parameter
chart is the original residue coefficient times its differential symbol. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  ParameterNeighborhood.sectionAlgebra ParameterChart.coordinateOrder
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R (c + g))
  [IsClosedImmersion f.left] [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (j : Fin (c + g + 1)) (B : ℕ) (hB : c + g + 1 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space R (c + g)).Opens) (hU : IsAffineOpen U)
  (i : Fin (c + g + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (s : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) s = LocalAdjunction.ideal X f U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) (List.ofFn s))
  (bI : Basis (Fin c) (LocalAdjunction.quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent)
  (hI : ∀ k, bI k = (LocalAdjunction.ideal X f U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) (LocalAdjunction.ideal X f U hU) s hs k))
  (bQ : Basis (Fin g) (LocalAdjunction.quotient X f U hU) Ω[LocalAdjunction.quotient X f U hU⁄R])
  (t : Fin g → Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U))
  (ht : ∀ k, bQ k = KaehlerDifferential.D R (LocalAdjunction.quotient X f U hU)
    (Ideal.Quotient.mk (LocalAdjunction.ideal X f U hU) (t k)))
  (b : Basis (Fin (c + g)) Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) Ω[Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)⁄R])
  (hb : (b : Fin (c + g) → Ω[Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)⁄R]) =
    Fin.append (fun k => KaehlerDifferential.D R Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) (s k))
      (fun k => KaehlerDifferential.D R Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) (t k)))
  (τ : Type u) [Fintype τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]

def symbolSections := Principal.PushforwardSectionCoordinates.sectionsMap f.left U
  (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
  (Principal.DifferentialSymbol.generator R X (IntrinsicOverlap.Intrinsic.model R (c + g)) f U g
    (fun k => f.left.app U (t k)))

include hI ht hb τ in
theorem comparison :
    (Affine.ModuleExactSections.sections U).map
      (ParameterGlobalCoordinates.iso X f (Nat.add_sub_cancel c g).symm
        j B hB (Nat.le_add_left g c)).hom =
      PrincipalResidueCoordinates.residueSections X f j B hB U hU i hUi s hs hreg b ≫
        symbolSections X f U t := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hglobal := ParameterGlobalSymbol.unit_symbol X f j B hB U hU i hUi
    s hs hreg bI hI bQ t ht b hb τ x
  have hsymbol := Closed.DifferentialSymbol.sections_quotient R X (IntrinsicOverlap.Intrinsic.model R (c + g)) f U hU g
    (fun k => f.left.app U (t k))
    (ParameterAdjunction.coefficient X f j B hB U hU i hUi s hs hreg b x)
  have hresidue := ConcreteCategory.congr_hom
    (PrincipalResidueCoordinates.residueSections_eq X f j B hB U hU i hUi s hs hreg b) x
  change _ = (symbolSections X f U t)
    (PrincipalResidueCoordinates.residueSections X f j B hB U hU i hUi s hs hreg b x)
  rw [hresidue]
  exact hglobal.trans hsymbol.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueLocalAdjunction
