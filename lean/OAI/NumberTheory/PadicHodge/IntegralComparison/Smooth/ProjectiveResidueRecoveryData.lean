import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionCoordinatesData
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureClassDegreeTransport

/-! # Projective Residue Recovery Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveResidueRecoveryData

noncomputable section

/-! The actual differential residue on a full projective point chart
is the local survivor used by the original global section recovery.
Its output is the original trace-one section class. -/
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
  ProjectiveFormTrace.composite_dimension
  ProjectivePoint.Survivor.coefficient_qc ProjectivePoint.Survivor.coefficient_finite

abbrev scalar := ProjectivePoint.KoszulMap.scalar i.left
abbrev pointMap := ProjectivePoint.KoszulMap.quotientMap s₀ i.left
abbrev forms := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g

local instance scalar_qc : (scalar X i).IsQuasicoherent :=
  Projective.ClosedImmersionPurity.directImage_quasicoherent i.left
local instance scalar_finite : (scalar X i).IsFiniteType :=
  Projective.ClosedImmersionPurity.directImage_finiteType i.left
local instance forms_qc : (forms (g := g) X).IsQuasicoherent :=
  FormCoherence.Integral.quasicoherent R X g

omit [IsNoetherianRing R] [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [IsClosedImmersion (Over.Hom.left i)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] [IsClosedImmersion s₀] in
theorem pureDegree : D.codimension=n+1-g := by have h := D.dimension; omega

include hB in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [IsClosedImmersion s₀] in
theorem exactAt (q : ℕ) (hq : q ≠ D.codimension) :
    (Projective.LocalAdjunction.dual X i (ProjectivePoint.Survivor.chart (R := R) (n := n)) B).ExactAt q :=
  Projective.TotalAdjunctionDimensionData.Residue.exactAt D.dimension X i
    (ProjectivePoint.Survivor.chart (R := R) (n := n)) B hB q hq

def adjunction := Projective.ParameterGlobalCoordinates.iso (c := D.codimension) (g := g) X i (pureDegree (X := X) (i := i) (s₀ := s₀) (g := g) (U := U) (hU := hU) (D := D))
  (ProjectivePoint.Survivor.chart (R := R) (n := n)) B hB (by have h := D.dimension; omega)

abbrev originalClass := ProjectivePoint.LocalSectionCoordinatesData.globalClass i.left s₀
  (ProjectiveSectionClassData.section_over X i s₀ hbase) B hB (scalar X i) (pointMap X i s₀)
  (exactAt X i s₀ B hB U hU D) (forms (g := g) X) (adjunction X i s₀ B hB U hU D)
  D.dimension (Projective.SectionClass.scalarUnitIso i.left s₀
    (ProjectiveSectionClassData.section_over X i s₀ hbase))

abbrev localClass := ProjectivePoint.LocalSectionCoordinatesData.localClass i.left s₀
  (ProjectiveSectionClassData.section_over X i s₀ hbase) B hB (scalar X i) (pointMap X i s₀)
  (exactAt X i s₀ B hB U hU D) (forms (g := g) X) (adjunction X i s₀ B hB U hU D)
  U hU D.equations D.parameters D.point_generates D.dimension

abbrev ordinaryMap := ProjectivePoint.LocalSectionCoordinatesData.ordinaryMap i.left s₀
  (forms (g := g) X) U hU D.contains D.equations D.parameters D.generates D.point_generates

def localMap := by
  letI : ∀ q, ((ProjectivePoint.GlobalTransferRecovery.coefficientDual B (scalar X i)).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc (scalar X i) (ProjectivePoint.Survivor.chart (R := R)) B (n+2) hB
  exact PrincipalPoint.PureCoordinates.localMap i.left U hU D.parameters
    (ProjectivePoint.GlobalTransferRecovery.coefficientDual B (scalar X i)) D.codimension
    (exactAt X i s₀ B hB U hU D) (forms (g := g) X) (adjunction X i s₀ B hB U hU D)
    (D.codimension+g)

include hB in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [GeometricallyConnected X.hom] [IsClosedImmersion s₀] in
theorem form_map :
    Projective.TotalAdjunctionDimensionData.Residue.rightMap D.dimension X i
      (ProjectivePoint.Survivor.chart (R := R) (n := n)) B hB U hU
      (PrincipalPoint.Fraction.family U D.parameters) (D.codimension+g) =
    localMap X i s₀ B hB U hU D := rfl

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [GeometricallyConnected X.hom] in
theorem form_eq : ProjectivePoint.ResidueData.form X i s₀ hbase B hB U hU D =
    localClass X i s₀ hbase B hB U hU D :=
  ConcreteCategory.congr_hom (form_map X i s₀ B hB U hU D)
    (ProjectivePoint.ResidueData.pointTransfer X i s₀ hbase B hB U hU D)

theorem originalClass_eq : originalClass X i s₀ hbase B hB U hU D =
    ProjectiveSectionClassData.sectionClass X i s₀ hbase B hB g := by
  exact Projective.PureClassDegreeTransport.comparison (scalar X i) (ProjectivePoint.Survivor.coefficient i.left s₀)
    ((Scheme.Modules.pushforward i.left).obj (forms (g := g) X)) B n (Fintype.card_fin (n+2)) hB
    (pointMap X i s₀)
    (Projective.SectionClass.scalarUnitIso i.left s₀
      (ProjectiveSectionClassData.section_over X i s₀ hbase))
    (Projective.SectionClass.pointUnitIso i.left s₀
      (ProjectiveSectionClassData.section_over X i s₀ hbase))
    D.codimension (n+1-g) (pureDegree (X := X) (i := i) (s₀ := s₀) (g := g) (U := U) (hU := hU) (D := D))
    (exactAt X i s₀ B hB U hU D)
    (ProjectiveSerre.exactAt i.left B n (Fintype.card_fin (n+2)) hB g)
    g ((Nat.add_comm g D.codimension).trans D.dimension)
    (ProjectiveSectionClassData.degree X i g)
    (ProjectiveFormTrace.adjunctionIso X i B hB g)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveResidueRecoveryData
