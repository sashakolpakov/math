import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterAdjunction

/-! # Parameter Adjunction Postcompose -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterAdjunctionPostcompose

noncomputable section

/-! Postcomposition of the checked affine parameter formula by the actual
closed-form section map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem postcompose {R : Type*} [CommRing R]
    {A B C : ModuleCat R} (f : A ⟶ B) (g : B ⟶ C)
    (x : A) (y : B) (h : f x = y) : (f ≫ g) x = g y := by
  rw [ModuleCat.comp_apply, h]

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
  (τ : Type u) [LinearOrder τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  (x : (Affine.ModuleExactSections.sections U).obj ((LocalAdjunction.dual X f j B).homology c))

abbrev symbol := postcompose _ (ParameterAdjunction.targetMap X f U hU τ) _ _
  (ParameterAdjunction.affine_symbol X f j B hB U hU i hUi s hs hreg bI hI bQ t ht b hb x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterAdjunctionPostcompose
