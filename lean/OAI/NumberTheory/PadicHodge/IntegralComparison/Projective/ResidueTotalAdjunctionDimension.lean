import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalAdjunctionDimensionData

/-! # Residue Total Adjunction Dimension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueTotalAdjunctionDimension

noncomputable section

/-! Transport the complete original residue statement in the ambient
index before supplying the dependent geometric data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module _root_.HomologicalComplex Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
attribute [local instance] MvPolynomial.gradedAlgebra
  LocalAdjunction.ambientAlgebra ParameterChart.coordinateOrder

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g N : ℕ}

def comparisonType (h : c + g = N) : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (j : Fin (N + 1)) (B : ℕ) (hB : N + 1 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)
  (i : Fin (N + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (s : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R N, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R N, U) s = LocalAdjunction.ideal X f U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R N, U) (List.ofFn s))
  (bI : Basis (Fin c) (LocalAdjunction.quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent)
  (_hI : ∀ k, bI k = (LocalAdjunction.ideal X f U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(IntrinsicOverlap.Intrinsic.space R N, U) (LocalAdjunction.ideal X f U hU) s hs k))
  (bQ : Basis (Fin g) (LocalAdjunction.quotient X f U hU) Ω[LocalAdjunction.quotient X f U hU⁄R])
  (t : Fin g → Γ(IntrinsicOverlap.Intrinsic.space R N, U))
  (_ht : ∀ k, bQ k = KaehlerDifferential.D R (LocalAdjunction.quotient X f U hU)
    (Ideal.Quotient.mk (LocalAdjunction.ideal X f U hU) (t k)))
  (b : Basis (Fin N) Γ(IntrinsicOverlap.Intrinsic.space R N, U) Ω[Γ(IntrinsicOverlap.Intrinsic.space R N, U)⁄R])
  (_hb : (fun k : Fin (c + g) => b (Fin.cast h k)) =
    Fin.append (fun k => KaehlerDifferential.D R Γ(IntrinsicOverlap.Intrinsic.space R N, U) (s k))
      (fun k => KaehlerDifferential.D R Γ(IntrinsicOverlap.Intrinsic.space R N, U) (t k)))
  (τ : Type u) [Fintype τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
    {ι : Type u} [LinearOrder ι] (W : ι → Principal.SectionPresheaf.Index U) (q : ℕ),
    TotalAdjunctionDimensionData.Residue.leftMap X f j B U hU i hUi s hs hreg t b W q = TotalAdjunctionDimensionData.Residue.rightMap h X f j B hB U hU W q

theorem comparison_sum : comparisonType (R := R) (c := c) (g := g) rfl := by
  intro X f hf hsm hp hrd j B hB U hU i hUi s hs hreg bI hI bQ t ht b hb τ hfin hpoly htower het ι hlin W q
  exact ResidueTotalAdjunction.comparison X f j B hB U hU i hUi
    s hs hreg bI hI bQ t ht b (by simpa using hb) τ W q

theorem comparison_all (h : c + g = N) : comparisonType (R := R) h := by
  cases h
  exact comparison_sum

abbrev comparison (h : c + g = N) := comparison_all (R := R) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueTotalAdjunctionDimension
