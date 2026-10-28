import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueClassData

/-! # Residue Map Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueMapData.Coordinates

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

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueClassData.Coordinates
attribute [local instance] ResidueClassData.Coordinates.sectionAlgebra
  ResidueClassData.Coordinates.scalar_qc
  ResidueClassData.Coordinates.scalar_finite
  ResidueClassData.Coordinates.line_qc
  Survivor.coefficient_qc Survivor.coefficient_finite

abbrev input :=
  (PrincipalReference.Concentration.Reference.functor U hU
    (ResidueData.family X i s₀ U hU D) (D.codimension+g)).obj
      (Survivor.dual i.left s₀ B)

abbrev normalInput :=
  (PrincipalReference.Concentration.Reference.functor U hU
    (ResidueData.family X i s₀ U hU D) (D.codimension+g)).obj
      (GlobalTransferRecovery.coefficientDual B
        (KoszulMap.scalar i.left))

abbrev refinementMap : input X i s₀ B U hU D ⟶ normalInput X i s₀ B U hU D := by
  let M := KoszulMap.scalar i.left
  let v := KoszulMap.quotientMap s₀ i.left
  letI (q : ℕ) : ((GlobalTransferRecovery.coefficientDual B M).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M
      (Survivor.chart (R := R) (n := n)) B (n+2) hB q
  letI (q : ℕ) : ((GlobalTransferRecovery.commonDual i.left s₀ B M v).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.common_dual_qc M (Survivor.coefficient i.left s₀)
      (Survivor.chart (R := R) (n := n)) B (n+2) hB v q
  letI := ProjectiveRefinement.DualMap.left_quasiIso M
    (Survivor.coefficient i.left s₀)
    (Survivor.chart (R := R) (n := n)) B (n+2) hB v
  exact Principal.RelativeTransfer.map U hU
    (ResidueData.family X i s₀ U hU D) (D.codimension+g)
    (GlobalTransferRecovery.left i.left s₀ B M v)
    (GlobalTransferRecovery.right i.left s₀ B M v)

abbrev output :=
  (Supported.CechHomotopyEquivalence.functor
    (ResidueData.family X i s₀ U hU D) (D.codimension+g)).obj
    ((single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U))
      (.up ℕ) D.codimension).obj (Principal.ClosedKoszulResidue.target i.left U hU))

def residueMap : normalInput X i s₀ B U hU D ⟶ output X i s₀ U hU D :=
  (Supported.CechHomotopyEquivalence.functor
    (ResidueData.family X i s₀ U hU D) (D.codimension+g)).map
    (Projective.TotalAdjunctionDimensionData.Residue.residue X i
      (Survivor.chart (R := R) (n := n)) B U hU D.coordinate D.below_coordinate
      D.equations D.generates D.regular D.ambientBasis)

abbrev residueFunction (y : input X i s₀ B U hU D) :=
  Koszul.RefinedResidueClass.residueClass Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)
    (Principal.SectionPresheaf.rings U hU) (ResidueData.family X i s₀ U hU D)
    D.equations D.parameters (PrincipalPoint.Fraction.units U hU D.parameters)
    (ResidueClassData.Coordinates.pointCoordinates X i s₀ B U hU D) R (Principal.TerminalScalars.bijective U hU) (n+1)
    (ScalarFraction.pure i.left s₀
      (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU)
    (ScalarFraction.zero i.left s₀
      (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU
      D.equations D.parameters D.point_generates)
    (ScalarFraction.pointQuotient i.left s₀
      (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) U hU D.contains
      D.equations D.parameters D.point_generates)
    (Principal.ClosedKoszulResidue.target i.left U hU)
    (Principal.ClosedKoszulResidue.pullback i.left U hU D.equations D.generates) y

abbrev native_comparison (y : input X i s₀ B U hU D) := by
  let hl := ResidueClassData.Coordinates.leftCoordinates X i s₀ B U hU D
  letI := Koszul.RefinedResidueClass.left_isIso Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)
    (Principal.SectionPresheaf.rings U hU) (ResidueData.family X i s₀ U hU D)
    D.equations _ _ _ hl (D.codimension+g)
  exact ResidueClassData.Coordinates.scalarCore X i s₀ hbase B hB U hU D
    (Principal.ClosedKoszulResidue.target i.left U hU)
    (Principal.ClosedKoszulResidue.pullback i.left U hU D.equations D.generates)
    (Principal.ClosedKoszulResidue.annihilated i.left U hU D.equations D.generates) _ hl y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueMapData.Coordinates
