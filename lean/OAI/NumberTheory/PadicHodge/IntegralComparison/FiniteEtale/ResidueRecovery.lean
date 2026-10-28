import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ResidueRecoveryData
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionCoordinates

/-! # Residue Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ResidueRecovery

noncomputable section

/-! The genuine finite-adjunction residue recovers the original
coefficient section class through the original projective comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
  [SmoothOfRelativeDimension g X.hom]
  (s₀ : Spec (CommRingCat.of R) ⟶ Y.left) (hbase : s₀ ≫ Y.hom = 𝟙 _)
  (B : ℕ) (hB : n+2≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i (s₀ ≫ f.left) g U hU)
attribute [local instance] IntegralComparison.Smooth.ProjectivePointTransfer.sourceSeparated
  IntegralComparison.Smooth.ProjectiveSectionClassData.composite_smooth
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_proper IntegralComparison.Smooth.ProjectiveFormTrace.composite_connected
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_dimension
  ProjectivePoint.Survivor.coefficient_qc ProjectivePoint.Survivor.coefficient_finite

abbrev original_recovery := by
  letI := ResidueRecoveryData.section_closed X Y f i s₀ hbase
  letI : (ResidueRecoveryData.coefficient X Y f i).IsQuasicoherent :=
    Finite.MapPureTrace.coefficients_quasicoherent f.left i.left
  letI : (ResidueRecoveryData.coefficient X Y f i).IsFiniteType :=
    Finite.MapPureTrace.coefficients_finiteType f.left i.left
  letI : (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g).IsQuasicoherent :=
    IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R Y g
  letI : (ResidueRecoveryData.forms (g := g) X Y f).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f.left
  exact ProjectivePoint.LocalSectionCoordinates.ordinary_recovery
    i.left (s₀ ≫ f.left) (SectionUnit.section_over X Y f i s₀ hbase) B hB
    (ResidueRecoveryData.coefficient X Y f i) (ResidueRecoveryData.pointMap X Y f i s₀) (ResidueRecoveryData.exactAt X Y f i s₀ B hB U hU D)
    (ResidueRecoveryData.forms (g := g) X Y f) (ResidueRecoveryData.adjunction X Y f i s₀ B hB U hU D)
    U hU D.contains D.equations D.parameters D.generates D.point_generates D.dimension
    (SectionUnit.coefficientUnit X Y f i s₀ hbase)

omit [Smooth X.hom] [GeometricallyConnected X.hom] in
theorem comparison :
    ResidueRecoveryData.ordinaryMap X Y f i s₀ hbase U hU D (ResidueRecoveryData.residue X Y f i s₀ hbase B hB U hU D) =
      SectionClassData.sectionClass X Y f i s₀ hbase B hB g := by
  rw [ResidueRecoveryData.residue_eq X Y f i s₀ hbase B hB U hU D]
  exact (original_recovery X Y f i s₀ hbase B hB U hU D).trans
    (ResidueRecoveryData.originalClass_eq X Y f i s₀ hbase B hB U hU D)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ResidueRecovery
