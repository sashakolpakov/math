import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueTotalAdjunctionDimension

/-! # Residue Total Adjunction Apply -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueTotalAdjunctionApply

noncomputable section

/-! Apply the original dimension-indexed residue comparison before
specializing its geometric data to a chosen projective point chart. -/

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

variable {ι : Type u} [LinearOrder ι]
  (W : ι → Principal.SectionPresheaf.Index U) (q : ℕ)

include hI ht hb τ in
theorem comparison
    (x : (PrincipalReference.Concentration.Reference.functor U hU W q).obj (LocalAdjunction.dual X f j B)) :
    TotalAdjunctionDimensionData.Residue.leftMap X f j B U hU i hUi
      s hs hreg t b W q x =
    TotalAdjunctionDimensionData.Residue.rightMap h X f j B hB U hU W q x :=
  ConcreteCategory.congr_hom
    (ResidueTotalAdjunctionDimension.comparison h X f j B hB U hU i hUi
      s hs hreg bI hI bQ t ht b hb τ W q) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueTotalAdjunctionApply
