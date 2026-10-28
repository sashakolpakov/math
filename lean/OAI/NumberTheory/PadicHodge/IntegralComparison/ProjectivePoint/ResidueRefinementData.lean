import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueMapData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DualRefinementMap

/-! # Residue Refinement Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueRefinementData.MapCoordinates

noncomputable section

/-! The original projective point residue has its literal ordinary
single-complex coordinate, with the point scalar and interchange sign
retained. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) [Nonempty X.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [SmoothOfRelativeDimension g X.hom]
  (s₀ : Spec (CommRingCat.of R) ⟶ X.left) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ X.hom = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (D : PointParameterData.Chart.Data X i s₀ g U hU)
attribute [local instance] IntegralComparison.Smooth.ProjectivePointTransfer.sourceSeparated
  IntegralComparison.Smooth.ProjectiveSectionClassData.composite_smooth
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_proper
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_connected

attribute [local instance] ResidueClassData.Coordinates.sectionAlgebra
  ResidueClassData.Coordinates.scalar_qc
  ResidueClassData.Coordinates.scalar_finite
  ResidueClassData.Coordinates.line_qc
  Survivor.coefficient_qc Survivor.coefficient_finite

abbrev leftChain := (Projective.NegativeRefinement.leftHom
  (KoszulMap.scalar i.left) (Survivor.coefficient i.left s₀)
  (Survivor.chart (R := R) (n := n)) B
  (KoszulMap.quotientMap s₀ i.left)).chainMap

abbrev rightChain := (Projective.NegativeRefinement.rightHom
  (KoszulMap.scalar i.left) (Survivor.coefficient i.left s₀)
  (Survivor.chart (R := R) (n := n)) B
  (KoszulMap.quotientMap s₀ i.left)).chainMap

abbrev nativeLeft := Principal.DualRefinementMap.nativeMap U hU
  (ScalarFraction.line (R := R) (n := n)) (leftChain X i s₀ B)

abbrev nativeRight := Principal.DualRefinementMap.nativeMap U hU
  (ScalarFraction.line (R := R) (n := n)) (rightChain X i s₀ B)

include hB in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem originalLeft_isIso :
    IsIso ((PrincipalReference.Concentration.Reference.functor U hU
      (ResidueData.family X i s₀ U hU D) (D.codimension+g)).map
      ((Affine.LocalDualInvariance.functor
        (ScalarFraction.line (R := R) (n := n))).map
          (leftChain X i s₀ B).op)) := by
  let M := KoszulMap.scalar i.left
  let v := KoszulMap.quotientMap s₀ i.left
  let (q : ℕ) : ((GlobalTransferRecovery.coefficientDual B M).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M
      (Survivor.chart (R := R) (n := n)) B (n+2) hB q
  let (q : ℕ) : ((GlobalTransferRecovery.commonDual i.left s₀ B M v).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.common_dual_qc M (Survivor.coefficient i.left s₀)
      (Survivor.chart (R := R) (n := n)) B (n+2) hB v q
  let := ProjectiveRefinement.DualMap.left_quasiIso M
    (Survivor.coefficient i.left s₀)
    (Survivor.chart (R := R) (n := n)) B (n+2) hB v
  exact Principal.RelativeTransfer.left_isIso U hU
    (ResidueData.family X i s₀ U hU D) (D.codimension+g)
    (GlobalTransferRecovery.left i.left s₀ B M v)

include hB in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem nativeLeft_isIso :
    IsIso ((Supported.CechHomotopyEquivalence.functor
      (ResidueData.family X i s₀ U hU D) (D.codimension+g)).map
      (nativeLeft X i s₀ B U hU)) := by
  let := originalLeft_isIso X i s₀ B hB U hU D
  exact Principal.DualRefinementMap.isIso U hU
    (ResidueData.family X i s₀ U hU D) (D.codimension+g)
    (ScalarFraction.line (R := R) (n := n)) (leftChain X i s₀ B)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueRefinementData.MapCoordinates
