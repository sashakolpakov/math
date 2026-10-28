import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueDimensionData
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.FiniteCoefficientResidueTotal

/-! # Coefficient Residue Dimension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueDimension

noncomputable section

/-! Transport the finite-coefficient residue comparison in the ambient
index before the dependent chart and parameter data are supplied. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
attribute [local instance] MvPolynomial.gradedAlgebra
  Projective.LocalAdjunction.ambientAlgebra Projective.ParameterChart.coordinateOrder
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra
  Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g N : ℕ}

def comparisonType (h : c+g=N) : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) (Y : Scheme.{u}) (f : Y ⟶ X.left)
  [IsFinite f] [Flat f] (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (j : Fin (N+1)) (B : ℕ) (hB : N+1≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)
  (k : Fin (N+1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (s : Fin c → Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) s = Projective.LocalAdjunction.ideal X i U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (List.ofFn s))
  (bI : Basis (Fin c) (Projective.LocalAdjunction.quotient X i U hU) (Projective.LocalAdjunction.ideal X i U hU).Cotangent)
  (_hI : ∀ a, bI a = (Projective.LocalAdjunction.ideal X i U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (Projective.LocalAdjunction.ideal X i U hU) s hs a))
  (bQ : Basis (Fin g) (Projective.LocalAdjunction.quotient X i U hU) Ω[Projective.LocalAdjunction.quotient X i U hU⁄R])
  (t : Fin g → Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U))
  (_ht : ∀ a, bQ a = KaehlerDifferential.D R (Projective.LocalAdjunction.quotient X i U hU)
    (Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X i U hU) (t a)))
  (b : Basis (Fin N) Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U)⁄R])
  (_hb : (fun a : Fin (c+g) => b (Fin.cast h a)) =
    Fin.append (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (s a))
      (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (t a)))
  (τ : Type u) [Fintype τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  {ι : Type u} [LinearOrder ι] (W : ι → Principal.SectionPresheaf.Index U) (q : ℕ)
  (x : Finite.FlatCoefficientSections.coefficientRing f i.left U),
    CoefficientResidueDimensionData.leftMap X f i j B U hU k hUk s hs hreg t b W q x =
      CoefficientResidueDimensionData.rightMap h X f i j B hB U hU W q x

theorem comparison_sum : comparisonType (R := R) (c := c) (g := g) rfl := by
  intro X Y f hf hflat i hi hsm hp hrd j B hB U hU k hUk s hs hreg bI hI bQ t ht b hb τ hfin hpoly htower het ι hlin W q x
  exact FiniteCoefficientResidueTotal.comparison X f i j B hB U hU k hUk
    s hs hreg bI hI bQ t ht b (by simpa using hb) τ W q x

theorem comparison_all (h : c+g=N) : comparisonType (R := R) h := by
  cases h
  exact comparison_sum

abbrev comparison (h : c+g=N) := comparison_all (R := R) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueDimension
