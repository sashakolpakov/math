import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueDimensionData
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueClass

/-! # Coefficient Residue Map Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueMapCoordinates

noncomputable section

/-! The actual finite adjunction residue uses the same principal
coefficient-resolution map as the fixed-point fraction formula. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Projective.LocalAdjunction.ambientAlgebra Projective.ParameterChart.coordinateOrder
  Finite.FlatCoefficientSections.quotientAlgebra
  Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (B : ℕ) (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (k : Fin (n+2)) (hUk : U ≤ OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (s : Fin c → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1),U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1),U) s = Projective.LocalAdjunction.ideal X i U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1),U) (List.ofFn s))
  (b : Basis (Fin (n+1)) Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1),U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1),U)⁄R])

abbrev frame := Projective.PrincipalResidueCoordinates.scalarFrame (c := n+1) (g := 0)
  (ProjectivePoint.Survivor.chart (R := R) (n := n)) U hU k hUk b

def raw (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    Principal.Koszul.Comparison.nativeComplex U hU
      (ProjectivePoint.ScalarFraction.line (R := R) (n := n))
      (CoefficientPointFraction.source f i.left B) ⟶
    (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤
      ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1),U)) (.up ℕ) c).obj
        (Principal.ClosedKoszulResidue.target i.left U hU) :=
  CoefficientResidueClass.residueMap f i.left B U hU k hUk
    (frame U hU k hUk b) s hs hreg x

omit [AlgebraicGeometry.Flat f] [Smooth X.hom] [IsProper X.hom] in
theorem native_eq (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    CoefficientResidueDimensionData.residue X f i
      (ProjectivePoint.Survivor.chart (R := R) (n := n)) B U hU k hUk s hs hreg b x =
    Principal.IntrinsicDualCoordinates.Intrinsic.map U hU
      (ProjectivePoint.ScalarFraction.line (R := R) (n := n))
      (CoefficientPointFraction.source f i.left B)
      (raw X f i B U hU k hUk s hs hreg b x) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueMapCoordinates
