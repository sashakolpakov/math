import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueNormalization

/-! # Residue Cochain Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueCochainCoordinates

noncomputable section

/-! The normal map inferred by the original scalar-fraction comparison
is the explicit normal comparison used by the point-residue coordinates.
The identity is proved on cochain maps, before supported homology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private abbrev homotopyTarget {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℕ} {a b : K ⟶ L} (_ : Homotopy a b) : K ⟶ L := b

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

abbrev originalNormalMap := homotopyTarget
  (ScalarFraction.leftCoordinates i.left s₀ B U hU
    D.coordinate D.below_coordinate (ResidueData.frame X i s₀ U hU D)
    D.equations D.generates D.regular)

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem normalMap_eq : originalNormalMap X i s₀ B U hU D =
    (ResidueClassData.Coordinates.normalCoordinates X i s₀ B U hU D).hom := rfl

abbrev originalResidueMap := originalNormalMap X i s₀ B U hU D ≫
  Principal.ClosedKoszulResidue.residue i.left U hU D.equations D.generates

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem residueMap_eq : originalResidueMap X i s₀ B U hU D =
    (ResidueClassData.Coordinates.normalCoordinates X i s₀ B U hU D).hom ≫
      Principal.ClosedKoszulResidue.residue i.left U hU D.equations D.generates :=
  congrArg (fun a => a ≫ Principal.ClosedKoszulResidue.residue i.left U hU
    D.equations D.generates) (normalMap_eq X i s₀ B U hU D)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueCochainCoordinates
