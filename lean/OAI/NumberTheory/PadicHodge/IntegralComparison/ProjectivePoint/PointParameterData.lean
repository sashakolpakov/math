import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionCharts
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution

/-! # Point Parameter Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart

noncomputable section

/-! Geometric data of a projective point chart: regular equations,
section parameters, and their actual conormal and differential bases. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] (z : Spec (CommRingCat.of R) ⟶ X.left)
  (g : ℕ) (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)

local instance ambientAlgebra : Algebra R Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (Projective.IntrinsicOverlap.Intrinsic.model R N) U

structure ParameterData where
  coordinate : Fin (N+1)
  below_coordinate : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) coordinate
  contains : ⊤ ≤ z ⁻¹ᵁ (f.left ⁻¹ᵁ U)
  codimension : ℕ
  dimension : codimension + g = N
  equations : Fin codimension → Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U)
  generates : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) equations = Projective.LocalAdjunction.ideal X f U hU
  regular : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (List.ofFn equations)
  conormalBasis : Module.Basis (Fin codimension) (Projective.LocalAdjunction.quotient X f U hU) (Projective.LocalAdjunction.ideal X f U hU).Cotangent
  conormalBasis_apply : ∀ i, conormalBasis i = (Projective.LocalAdjunction.ideal X f U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (Projective.LocalAdjunction.ideal X f U hU) equations generates i)
  parameters : Fin g → Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U)
  quotientBasis : Module.Basis (Fin g) (Projective.LocalAdjunction.quotient X f U hU) Ω[Projective.LocalAdjunction.quotient X f U hU⁄R]
  quotientBasis_apply : ∀ i, quotientBasis i = KaehlerDifferential.D R (Projective.LocalAdjunction.quotient X f U hU)
    (Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X f U hU) (parameters i))
  point_generates : KoszulPartial.Resolution.pointIdeal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) equations parameters =
    (z ≫ f.left).ker.ideal ⟨U,hU⟩
  point_regular : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U)
    (List.ofFn (Fin.append equations parameters))
  coordinateIndex : Type u
  finiteVariables : Fintype coordinateIndex
  coordinates : Algebra (MvPolynomial coordinateIndex R)
    (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
  coordinateTower : letI := coordinates
    IsScalarTower R (MvPolynomial coordinateIndex R)
      (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
  coordinateEtale : letI := coordinates
    Algebra.Etale (MvPolynomial coordinateIndex R)
      (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))

structure Data extends ParameterData X f z g U hU where
  ambientBasis : Module.Basis (Fin N) Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U)⁄R]
  ambientBasis_apply :
    (fun i : Fin (codimension+g) => ambientBasis (Fin.cast dimension i)) =
      Fin.append
        (fun i => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (equations i))
        (fun i => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (parameters i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart
