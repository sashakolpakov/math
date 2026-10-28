import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveResidueRecoveryData
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionCoordinates

/-! # Projective Residue Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveResidueRecovery

noncomputable section

/-! The literal differential residue recovers the original trace-one section class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) [Nonempty X.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [SmoothOfRelativeDimension g X.hom]
  (s₀ : Spec (CommRingCat.of R) ⟶ X.left) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ X.hom = 𝟙 _) (B : ℕ) (hB : n+2≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i s₀ g U hU)
attribute [local instance] ProjectivePointTransfer.sourceSeparated
  ProjectiveSectionClassData.composite_smooth
  ProjectiveFormTrace.composite_proper ProjectiveFormTrace.composite_connected

attribute [local instance] ProjectiveResidueRecoveryData.scalar_qc ProjectiveResidueRecoveryData.scalar_finite ProjectiveResidueRecoveryData.forms_qc

abbrev original_recovery := ProjectivePoint.LocalSectionCoordinates.ordinary_recovery
  i.left s₀ (ProjectiveSectionClassData.section_over X i s₀ hbase) B hB
  (ProjectiveResidueRecoveryData.scalar X i) (ProjectiveResidueRecoveryData.pointMap X i s₀) (ProjectiveResidueRecoveryData.exactAt X i s₀ B hB U hU D)
  (ProjectiveResidueRecoveryData.forms (g := g) X) (ProjectiveResidueRecoveryData.adjunction X i s₀ B hB U hU D)
  U hU D.contains D.equations D.parameters D.generates D.point_generates D.dimension
  (Projective.SectionClass.scalarUnitIso i.left s₀
    (ProjectiveSectionClassData.section_over X i s₀ hbase))

theorem comparison :
    ProjectiveResidueRecoveryData.ordinaryMap X i s₀ U hU D (ProjectivePoint.ResidueData.form X i s₀ hbase B hB U hU D) =
      ProjectiveSectionClassData.sectionClass X i s₀ hbase B hB g := by
  rw [ProjectiveResidueRecoveryData.form_eq X i s₀ hbase B hB U hU D]
  exact (original_recovery X i s₀ hbase B hB U hU D).trans
    (ProjectiveResidueRecoveryData.originalClass_eq X i s₀ hbase B hB U hU D)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveResidueRecovery
