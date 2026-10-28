import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueTotalCoordinates

/-! # Finite Coefficient Residue Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.FiniteCoefficientResidueTotal

noncomputable section

/-! Typed supported-total form of the original finite coefficient residue. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module Opposite _root_.HomologicalComplex
private theorem factor {A : Type*} [Category A]
    {P Q S T V W : A} {r : P ⟶ T} {a : P ⟶ Q} {b : Q ⟶ S}
    {u : S ⟶ T} {v : T ⟶ W} {d : S ⟶ V} {e : V ⟶ W}
    (hr : r = a ≫ b ≫ u) (he : d ≫ e = u ≫ v) :
    r ≫ v = a ≫ b ≫ d ≫ e := by
  rw [hr]
  simp only [Category.assoc]
  rw [← he]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Projective.LocalAdjunction.ambientAlgebra Projective.ParameterChart.coordinateOrder
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra
  Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
attribute [local instance] ProjectiveCoefficient.HomLocal.scalar_terms
  ProjectiveCoefficient.HomLocal.coefficient_terms
variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (c+g)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (j : Fin (c+g+1)) (B : ℕ) (hB : c+g+1≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (c+g)).Opens) (hU : IsAffineOpen U)
  (k : Fin (c+g+1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (s : Fin c → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) s = Projective.LocalAdjunction.ideal X i U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (List.ofFn s))
  (bI : Basis (Fin c) (Projective.LocalAdjunction.quotient X i U hU) (Projective.LocalAdjunction.ideal X i U hU).Cotangent)
  (hI : ∀ a, bI a = (Projective.LocalAdjunction.ideal X i U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (Projective.LocalAdjunction.ideal X i U hU) s hs a))
  (bQ : Basis (Fin g) (Projective.LocalAdjunction.quotient X i U hU) Ω[Projective.LocalAdjunction.quotient X i U hU⁄R])
  (t : Fin g → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U))
  (ht : ∀ a, bQ a = KaehlerDifferential.D R (Projective.LocalAdjunction.quotient X i U hU)
    (Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X i U hU) (t a)))
  (b : Basis (Fin (c+g)) Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U)⁄R])
  (hb : (b : Fin (c+g) → Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U)⁄R]) =
    Fin.append (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (s a))
      (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (t a)))
  (τ : Type u) [Fintype τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]

variable {ι : Type u} [LinearOrder ι]
  (W : ι → Principal.SectionPresheaf.Index U) (q : ℕ)

include hI ht hb τ in
theorem comparison (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    CoefficientResidueDimensionData.leftMap
      (R := R) (c := c) (g := g) (N := c+g) X f i j B U hU k hUk
      s hs hreg t b W q x =
    CoefficientResidueDimensionData.rightMap
      (R := R) (c := c) (g := g) (N := c+g) rfl X f i j B hB U hU W q x :=
  factor
    (CoefficientResidueTotalCoordinates.concentration
      X f i j B hB U hU k hUk s hs hreg b W q x)
    (CoefficientResidueTotalCoordinates.adjunction
      X f i j B hB U hU k hUk s hs hreg bI hI bQ t ht b hb τ W q x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.FiniteCoefficientResidueTotal
