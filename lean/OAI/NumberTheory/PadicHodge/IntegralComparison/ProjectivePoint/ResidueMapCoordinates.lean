import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueIntrinsicMaps

/-! # Residue Map Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueMapCoordinates

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

private theorem apply_comp_eq {S : Type*} [Ring S] {P Q T : ModuleCat S}
    {f f' : Q ⟶ T} {g g' : P ⟶ Q} (hf : f = f') (hg : g = g') (x : P) :
    f (g x) = f' (g' x) := by
  cases hf
  cases hg
  rfl

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem map_comparison (y : ResidueMapData.Coordinates.input X i s₀ B U hU D) :
    ResidueMapData.Coordinates.residueMap X i s₀ B U hU D
      (ResidueMapData.Coordinates.refinementMap X i s₀ B hB U hU D y) =
    ResidueMapData.Coordinates.residueFunction X i s₀ hbase B hB U hU D y := by
  have h := apply_comp_eq (ResidueIntrinsicMaps.MapCoordinates.residueMap_eq X i s₀ B U hU D)
    (ResidueIntrinsicMaps.MapCoordinates.refinementMap_eq X i s₀ B hB U hU D) y
  exact h.trans (ResidueMapData.Coordinates.native_comparison X i s₀ hbase B hB U hU D y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueMapCoordinates
