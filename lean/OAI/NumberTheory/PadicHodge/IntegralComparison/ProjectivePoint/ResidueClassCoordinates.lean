import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueMapCoordinates

/-! # Residue Class Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueClassCoordinates

noncomputable section

/-! The original projective point residue has its literal ordinary
single-complex coordinate, with the point scalar and interchange sign
retained. -/
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

attribute [local instance] ResidueClassData.Coordinates.sectionAlgebra ResidueClassData.Coordinates.scalar_qc ResidueClassData.Coordinates.scalar_finite ResidueClassData.Coordinates.line_qc

private abbrev pointInput := LocalCoordinates.pointAt i.left s₀
  (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU
  D.equations D.parameters D.point_generates D.dimension

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
private theorem refinement_at_point :
    ResidueMapData.Coordinates.refinementMap X i s₀ B hB U hU D
        (pointInput X i s₀ hbase B hB U hU D) =
      ResidueData.pointTransfer X i s₀ hbase B hB U hU D := rfl

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
private theorem residue_at_point :
    ResidueMapData.Coordinates.residueFunction X i s₀ hbase B hB U hU D
        (pointInput X i s₀ hbase B hB U hU D) =
      ResidueClassData.Coordinates.rawResidue X i s₀ hbase B hB U hU D := rfl

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
private theorem actual_residue_def :
    ResidueData.residue X i s₀ hbase B hB U hU D =
      ResidueMapData.Coordinates.residueMap X i s₀ B U hU D
        (ResidueData.pointTransfer X i s₀ hbase B hB U hU D) := rfl

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem residue_coordinates :
    ResidueData.residue X i s₀ hbase B hB U hU D =
      ResidueClassData.Coordinates.rawResidue X i s₀ hbase B hB U hU D := by
  rw [actual_residue_def X i s₀ hbase B hB U hU D,
    ← refinement_at_point X i s₀ hbase B hB U hU D]
  exact (ResidueMapCoordinates.map_comparison X i s₀ hbase B hB U hU D
    (pointInput X i s₀ hbase B hB U hU D)).trans
      (residue_at_point X i s₀ hbase B hB U hU D)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueClassCoordinates
