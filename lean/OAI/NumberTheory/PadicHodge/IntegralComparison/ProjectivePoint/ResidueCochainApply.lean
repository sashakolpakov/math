import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueCochainCoordinates

/-! # Residue Cochain Apply -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueCochainApply

noncomputable section

/-! Evaluation of the original scalar residue map in supported homology,
with its input kept arbitrary. -/
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
  ResidueClassData.Coordinates.sectionAlgebra
  ResidueClassData.Coordinates.scalar_qc
  ResidueClassData.Coordinates.scalar_finite
  ResidueClassData.Coordinates.line_qc

def originalMap : ResidueMapData.Coordinates.normalInput X i s₀ B U hU D ⟶
    ResidueMapData.Coordinates.output X i s₀ U hU D :=
    (Supported.CechHomotopyEquivalence.functor
      (ResidueData.family X i s₀ U hU D) (D.codimension+g)).map
      (ResidueCochainCoordinates.originalResidueMap X i s₀ B U hU D)

abbrev coordinateMap : ResidueMapData.Coordinates.normalInput X i s₀ B U hU D ⟶
    ResidueMapData.Coordinates.output X i s₀ U hU D :=
  ResidueIntrinsicMaps.MapCoordinates.nativeResidueMap X i s₀ B U hU D

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem map_eq : originalMap X i s₀ B U hU D = coordinateMap X i s₀ B U hU D :=
  congrArg (fun a => (Supported.CechHomotopyEquivalence.functor
    (ResidueData.family X i s₀ U hU D) (D.codimension+g)).map a)
    (ResidueCochainCoordinates.residueMap_eq X i s₀ B U hU D)

attribute [local irreducible] HomologicalComplex.homology

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem comparison (y : ResidueMapData.Coordinates.normalInput X i s₀ B U hU D) :
    originalMap X i s₀ B U hU D y = coordinateMap X i s₀ B U hU D y :=
  ConcreteCategory.congr_hom (map_eq X i s₀ B U hU D) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueCochainApply
