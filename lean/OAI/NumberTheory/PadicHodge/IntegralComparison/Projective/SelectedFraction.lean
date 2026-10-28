import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SelectedFractionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelPrincipalSheaf

/-! # Selected Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SelectedFraction.Coordinates

noncomputable section

/-! The actual selected projective residue gives the native fraction
input with its original codimension sign and the same Witt coefficient. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  [IsNoetherianRing (SelectedFractionCoordinates.baseRing p k n)] [Module.Injective (SelectedFractionCoordinates.baseRing p k n) (SelectedFractionCoordinates.baseRing p k n)]
  [IsArtinianRing (SelectedFractionCoordinates.baseRing p k n)] [IsLocalRing (SelectedFractionCoordinates.baseRing p k n)] {d g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of (SelectedFractionCoordinates.baseRing p k n)))) [Nonempty X.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom]
  (i : X ⟶ IntrinsicOverlap.Intrinsic.model (SelectedFractionCoordinates.baseRing p k n) (d+1)) [IsClosedImmersion i.left]
  (s₀ : Spec (CommRingCat.of (SelectedFractionCoordinates.baseRing p k n)) ⟶ X.left) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ X.hom = 𝟙 _) (B : ℕ) (hB : d+2 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space (SelectedFractionCoordinates.baseRing p k n) (d+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i s₀ g U hU)
  (Y : Over (Spec (CommRingCat.of (SelectedFractionCoordinates.baseRing p k n))))
  [Smooth Y.hom] [IsProper Y.hom] [Y.left.IsSeparated] [SmoothOfRelativeDimension g Y.hom]
  (f : Y ⟶ X)
  (Z : Over (Spec (CommRingCat.of k))) [IsSeparated Z.hom]
  (j : Z.left ⟶ Y.left)
  (hp : IsPullback j Z.hom Y.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (V : Y.left.affineOpens) (hVU : V.val ≤ (f ≫ i).left ⁻¹ᵁ U)
  (z : Γ(Y.left,(f ≫ i).left ⁻¹ᵁ U))

attribute [local instance] IntegralComparison.Smooth.ProjectivePointTransfer.sourceSeparated
  IntegralComparison.Smooth.ProjectiveSectionClassData.composite_smooth
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_proper IntegralComparison.Smooth.ProjectiveFormTrace.composite_connected

variable (r : WittVector p k) (hr : Truncated.Witt.quotient p k n r = SelectedFractionCoordinates.rawValue p k n X i s₀ hbase B hB U hU D)

variable {κ : Type} [CommRing κ] (η : Γ(Y.left,V.val) →+* κ)
  (hk : Koszul.OrientedTopCohomology.ideal Γ(Y.left,V.val)
    (PrincipalResidue.ResidueRestriction.parameters (f ≫ i).left U V.val hVU D.parameters) = RingHom.ker η)
  (hz : η (Y.left.presheaf.map (homOfLE hVU).op z) = 1)

include hk hz hr in
omit [IsArtinianRing (SelectedFractionCoordinates.baseRing p k n)] [IsLocalRing (SelectedFractionCoordinates.baseRing p k n)] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] [IsProper Y.hom] [Y.left.IsSeparated] [SmoothOfRelativeDimension g Y.hom] [IsSeparated Z.hom] in
theorem native_input :
    TruncatedModel.ModelPrincipalSheaf.input p k n Y (IntrinsicOverlap.Intrinsic.model (SelectedFractionCoordinates.baseRing p k n) (d+1))
      (f ≫ i) U V hVU g D.codimension D.parameters
      (ULift.up.{2,1} (ULift.up.{1,0}
        (SelectedFractionCoordinates.nativeClass p k n X i s₀ hbase B hB U hU D Y f V hVU z))) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      TruncatedModel.ModelPrincipalFraction.input p k n Y Z j hp V g
        (TruncatedModel.ResidueFraction.localParameters p k n Y
          (IntrinsicOverlap.Intrinsic.model (SelectedFractionCoordinates.baseRing p k n) (d+1)) (f ≫ i) U V hVU g D.parameters) D.codimension r := by
  exact TruncatedModel.ModelPrincipalSheaf.weighted p k n Y Z j hp
    (IntrinsicOverlap.Intrinsic.model (SelectedFractionCoordinates.baseRing p k n) (d+1)) (f ≫ i) U V hVU g D.codimension D.parameters
    (SelectedFractionCoordinates.nativeClass p k n X i s₀ hbase B hB U hU D Y f V hVU z)
    (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g) r
    (SelectedFractionCoordinates.coordinates p k n X i s₀ hbase B hB U hU D Y f Z j hp V hVU z r hr η hk hz)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SelectedFraction.Coordinates
