import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionCoordinatesData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureClassDegreeTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleAdjunctionPairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectivePointTransfer

/-! # Residue Recovery Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ResidueRecoveryData

noncomputable section

/-! The actual finite-adjunction residue is the local survivor of the
original coefficient section class, in the original projective coordinates. -/
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

local instance projectiveSeparated : (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).left.IsSeparated := by
  change (Proj (homogeneousSubmodule (Fin (n+2)) R)).IsSeparated
  constructor
  rw [← terminal.comp_from (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))]
  infer_instance

abbrev coefficient := Cech.StructurePullbackUnit.coefficients f.left i.left
abbrev pointMap := Cech.SectionCoefficientUnit.sheafMap s₀ f.left i.left
abbrev forms := (Scheme.Modules.pushforward f.left).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g)

include i hbase in
omit [IsNoetherianRing R] [Module.Injective R R] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] in
theorem section_closed : IsClosedImmersion (s₀ ≫ f.left) := by
  let : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  exact isClosedImmersion_of_comp_eq_id (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (s₀ ≫ f.left)
    (SectionUnit.section_over X Y f i s₀ hbase)

local instance coefficient_qc : (coefficient X Y f i).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f.left i.left
local instance coefficient_finite : (coefficient X Y f i).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType f.left i.left
local instance forms_qc : (forms (g := g) X Y f).IsQuasicoherent := by
  let : (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g).IsQuasicoherent :=
    IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R Y g
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f.left

omit [IsNoetherianRing R] [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] [SmoothOfRelativeDimension g X.hom] in
theorem pureDegree : D.codimension=n+1-g := by have h := D.dimension; omega

include hB in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty X.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] in
theorem exactAt (q : ℕ) (hq : q ≠ D.codimension) :
    (ProjectiveCoefficient.HomLocal.coefficientDual X f.left i
      (ProjectivePoint.Survivor.chart (R := R) (n := n)) B).ExactAt q :=
  ProjectiveFinite.CoefficientResidueDimensionData.exactAt D.dimension X f.left i
    (ProjectivePoint.Survivor.chart (R := R) (n := n)) B hB q hq

def adjunction := AdjunctionDegreeCoordinates.iso X Y f i g D.codimension
  (pureDegree (X := X) (Y := Y) (f := f) (i := i) (s₀ := s₀) (g := g) (U := U) (hU := hU) (D := D)) (ProjectivePoint.Survivor.chart (R := R) (n := n)) B hB (by have h := D.dimension; omega)

def coefficientLocal := by
  letI := section_closed X Y f i s₀ hbase
  exact ProjectivePoint.CoefficientLocalClass.value i.left (s₀ ≫ f.left)
    (SectionUnit.section_over X Y f i s₀ hbase) B hB
    (coefficient X Y f i) (pointMap X Y f i s₀) U hU
    D.equations D.parameters D.point_generates D.dimension

def originalClass := by
  letI := section_closed X Y f i s₀ hbase
  exact ProjectivePoint.LocalSectionCoordinatesData.globalClass i.left (s₀ ≫ f.left)
    (SectionUnit.section_over X Y f i s₀ hbase) B hB
    (coefficient X Y f i) (pointMap X Y f i s₀)
    (exactAt X Y f i s₀ B hB U hU D) (forms (g := g) X Y f)
    (adjunction X Y f i s₀ B hB U hU D) D.dimension
    (SectionUnit.coefficientUnit X Y f i s₀ hbase)

def localClass := by
  letI := section_closed X Y f i s₀ hbase
  exact ProjectivePoint.LocalSectionCoordinatesData.localClass i.left (s₀ ≫ f.left)
    (SectionUnit.section_over X Y f i s₀ hbase) B hB
    (coefficient X Y f i) (pointMap X Y f i s₀)
    (exactAt X Y f i s₀ B hB U hU D) (forms (g := g) X Y f)
    (adjunction X Y f i s₀ B hB U hU D) U hU
    D.equations D.parameters D.point_generates D.dimension

def ordinaryMap := by
  letI := section_closed X Y f i s₀ hbase
  exact ProjectivePoint.LocalSectionCoordinatesData.ordinaryMap i.left (s₀ ≫ f.left)
    (forms (g := g) X Y f) U hU D.contains D.equations D.parameters D.generates D.point_generates

def localMap := by
  letI : ∀ q, ((ProjectivePoint.GlobalTransferRecovery.coefficientDual B
      (coefficient X Y f i)).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc (coefficient X Y f i) (ProjectivePoint.Survivor.chart (R := R)) B (n+2) hB
  exact PrincipalPoint.PureCoordinates.localMap i.left U hU D.parameters
    (ProjectivePoint.GlobalTransferRecovery.coefficientDual B (coefficient X Y f i))
    D.codimension (exactAt X Y f i s₀ B hB U hU D) (forms (g := g) X Y f)
    (adjunction X Y f i s₀ B hB U hU D) (D.codimension+g)

def residue := Principal.FiniteEtaleAdjunctionPairing.finiteMap D.dimension X Y f i
  (ProjectivePoint.Survivor.chart (R := R) (n := n)) B hB U hU (PrincipalPoint.Fraction.family U D.parameters)
  (D.codimension+g) (coefficientLocal X Y f i s₀ hbase B hB U hU D)

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] in
theorem residue_map :
    Principal.FiniteEtaleAdjunctionPairing.finiteMap D.dimension X Y f i
      (ProjectivePoint.Survivor.chart (R := R) (n := n)) B hB U hU (PrincipalPoint.Fraction.family U D.parameters)
      (D.codimension+g) = localMap X Y f i s₀ B hB U hU D := by
  let : ∀ q, ((ProjectivePoint.GlobalTransferRecovery.coefficientDual B
      (coefficient X Y f i)).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc (coefficient X Y f i) (ProjectivePoint.Survivor.chart (R := R)) B (n+2) hB
  exact (PrincipalPoint.PureCoordinates.localMap_eq i.left U hU D.parameters
    (ProjectivePoint.GlobalTransferRecovery.coefficientDual B (coefficient X Y f i))
    D.codimension (exactAt X Y f i s₀ B hB U hU D) (forms (g := g) X Y f)
    (adjunction X Y f i s₀ B hB U hU D) (D.codimension+g)).symm

omit [Nonempty ↥X.left] [Smooth X.hom] [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] in
theorem residue_eq : residue X Y f i s₀ hbase B hB U hU D =
    localClass X Y f i s₀ hbase B hB U hU D :=
  ConcreteCategory.congr_hom (residue_map X Y f i s₀ B hB U hU D)
    (coefficientLocal X Y f i s₀ hbase B hB U hU D)

omit [Smooth X.hom] [GeometricallyConnected X.hom] in
theorem originalClass_eq : originalClass X Y f i s₀ hbase B hB U hU D =
    SectionClassData.sectionClass X Y f i s₀ hbase B hB g := by
  let := section_closed X Y f i s₀ hbase
  exact Projective.PureClassDegreeTransport.comparison (coefficient X Y f i)
    (ProjectivePoint.Survivor.coefficient i.left (s₀ ≫ f.left))
    ((Scheme.Modules.pushforward i.left).obj (forms (g := g) X Y f))
    B n (Fintype.card_fin (n+2)) hB (pointMap X Y f i s₀)
    (SectionUnit.coefficientUnit X Y f i s₀ hbase)
    (Projective.SectionClass.pointUnitIso i.left (s₀ ≫ f.left)
      (SectionUnit.section_over X Y f i s₀ hbase))
    D.codimension (n+1-g) (pureDegree (X := X) (Y := Y) (f := f) (i := i) (s₀ := s₀) (g := g) (U := U) (hU := hU) (D := D))
    (exactAt X Y f i s₀ B hB U hU D)
    (Finite.MapCoefficientPurity.exactAt f.left i.left B n (Fintype.card_fin (n+2)) hB g)
    g ((Nat.add_comm g D.codimension).trans D.dimension) (ProperTraceBase.degree X i g)
    (ProjectiveFinite.EtaleAdjunction.iso X Y f i g (ProjectivePoint.Survivor.chart (R := R) (n := n)) B hB
      (ProperTraceBase.dimension_le X i g))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ResidueRecoveryData
