import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueRefinementCoordinates

/-! # Residue Intrinsic Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueIntrinsicMaps.MapCoordinates

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

def nativeRefinementMap : ResidueMapData.Coordinates.input X i s₀ B U hU D ⟶ ResidueMapData.Coordinates.normalInput X i s₀ B U hU D := by
  letI := ResidueRefinementData.MapCoordinates.nativeLeft_isIso X i s₀ B hB U hU D
  exact (Supported.CechHomotopyEquivalence.functor
    (ResidueData.family X i s₀ U hU D) (D.codimension+g)).map
    (ResidueRefinementData.MapCoordinates.nativeRight X i s₀ B U hU) ≫
      inv ((Supported.CechHomotopyEquivalence.functor
        (ResidueData.family X i s₀ U hU D) (D.codimension+g)).map
        (ResidueRefinementData.MapCoordinates.nativeLeft X i s₀ B U hU))

def nativeResidueMap : ResidueMapData.Coordinates.normalInput X i s₀ B U hU D ⟶ ResidueMapData.Coordinates.output X i s₀ U hU D :=
  (Supported.CechHomotopyEquivalence.functor
    (ResidueData.family X i s₀ U hU D) (D.codimension+g)).map
    ((ResidueClassData.Coordinates.normalCoordinates X i s₀ B U hU D).hom ≫
      Principal.ClosedKoszulResidue.residue i.left U hU D.equations D.generates)

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem refinementMap_eq :
    ResidueMapData.Coordinates.refinementMap X i s₀ B hB U hU D = nativeRefinementMap X i s₀ B hB U hU D :=
  ResidueRefinementCoordinates.Map.refinement_coordinates X i s₀ B hB U hU D

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] [IsClosedImmersion s₀] in
theorem residueMap_eq :
    ResidueMapData.Coordinates.residueMap X i s₀ B U hU D = nativeResidueMap X i s₀ B U hU D := by
  dsimp only [ResidueMapData.Coordinates.residueMap, nativeResidueMap]
  rw [ResidueClassData.Coordinates.map_coordinates X i s₀ B U hU D]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueIntrinsicMaps.MapCoordinates
