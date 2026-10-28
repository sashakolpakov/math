import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CoefficientLocalClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueTotalAdjunctionApply
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectivePointTransfer

/-! # Residue Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueData

noncomputable section

/-! The genuine projective point chart supplies the original scalar
residue and its differential-form image on one fixed principal diagram. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

local instance scalar_qc : (KoszulMap.scalar i.left).IsQuasicoherent :=
  Projective.ClosedImmersionPurity.directImage_quasicoherent i.left
local instance scalar_finite : (KoszulMap.scalar i.left).IsFiniteType :=
  Projective.ClosedImmersionPurity.directImage_finiteType i.left

abbrev family := PrincipalPoint.Fraction.family U D.parameters
abbrev frame := Projective.PrincipalResidueCoordinates.scalarFrame (c := n+1) (g := 0)
  (Survivor.chart (R := R) (n := n)) U hU D.coordinate D.below_coordinate D.ambientBasis

abbrev pointTransfer := CoefficientLocalClass.value i.left s₀
  (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB
  (KoszulMap.scalar i.left)
  (KoszulMap.quotientMap s₀ i.left)
  U hU D.equations D.parameters D.point_generates D.dimension

abbrev residue :=
  (Supported.CechHomotopyEquivalence.functor (family X i s₀ U hU D) (D.codimension+g)).map
    (Projective.TotalAdjunctionDimensionData.Residue.residue X i
      (Survivor.chart (R := R) (n := n)) B U hU D.coordinate D.below_coordinate
      D.equations D.generates D.regular D.ambientBasis)
    (pointTransfer X i s₀ hbase B hB U hU D)

abbrev form := Projective.TotalAdjunctionDimensionData.Residue.rightMap D.dimension X i
  (Survivor.chart (R := R) (n := n)) B hB U hU
  (family X i s₀ U hU D) (D.codimension+g)
  (pointTransfer X i s₀ hbase B hB U hU D)

abbrev differential :=
  (Supported.CechHomotopyEquivalence.functor (family X i s₀ U hU D) (D.codimension+g)).map
    (Projective.TotalAdjunctionDimensionData.Residue.symbol X i U hU D.parameters)
    (residue X i s₀ hbase B hB U hU D)

abbrev comparison := by
  letI := D.finiteVariables
  letI := D.coordinates
  letI := D.coordinateTower
  letI := D.coordinateEtale
  exact Projective.ResidueTotalAdjunctionApply.comparison D.dimension X i
      (Survivor.chart (R := R) (n := n)) B hB U hU
      D.coordinate D.below_coordinate D.equations D.generates D.regular
      D.conormalBasis D.conormalBasis_apply D.quotientBasis D.parameters D.quotientBasis_apply
      D.ambientBasis D.ambientBasis_apply D.coordinateIndex
      (family X i s₀ U hU D) (D.codimension+g)
    (pointTransfer X i s₀ hbase B hB U hU D)

abbrev residue_eq :=
  ResidueClass.fixedPoint i.left s₀
    (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU D.contains
    D.coordinate D.below_coordinate (frame X i s₀ U hU D)
    D.equations D.parameters D.generates D.point_generates D.regular D.point_regular D.dimension

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueData
