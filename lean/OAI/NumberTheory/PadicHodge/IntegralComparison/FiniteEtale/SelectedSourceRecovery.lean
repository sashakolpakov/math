import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.SelectedFixed
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ResidueRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SourceIntrinsicRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FiberPrincipalSupport
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionSourceCoordinates

/-! # Selected Source Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SelectedSourceRecovery

noncomputable section

/-! The original finite point section is recovered by the actual
selected native principal comparison. Scalar fixedness and all support
conditions are derived from the selected fiber component. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem join_equalities {A : Type*} {a b c d : A}
    (hab : a = b) (hcd : c = d) (hbc : b = c) : a = d :=
  hab.trans (hbc.trans hcd)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra IntegralComparison.Finite.FlatCoefficientSections.quotientAlgebra IntegralComparison.Finite.FlatCoefficientSections.coefficientAlgebra IntegralComparison.Finite.FlatCoefficientSections.ambientAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
  [SmoothOfRelativeDimension g X.hom]
  (s₀ : Spec (CommRingCat.of R) ⟶ Y.left) (hbase : s₀ ≫ Y.hom = 𝟙 _)
  (B : ℕ) (hB : n+2≤B) (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i (s₀ ≫ f.left) g U hU)
  (hgood : TraceBasis.Good R Y X f (i.left ⁻¹ᵁ U))
  (z : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U)
  (hz :
    letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i.left ⁻¹ᵁ U)
    letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
    letI := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains
    letI : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := hgood.2.2
    letI : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := f.left.finite_app _ hgood.1
    letI : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
      AffineOpen.DeRhamTrace.sectionEtale R Y X f (i.left ⁻¹ᵁ U) hgood.1
    (1 ⊗ₜ[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U] z : R ⊗[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U] IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) =
      FiberSectionTrace.component (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) R
        (IntegralComparison.Finite.SectionEvaluation.evaluation R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains))
  (he :
    letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i.left ⁻¹ᵁ U)
    letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
    letI := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains
    IntegralComparison.Finite.SectionEvaluation.evaluation R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains z = 1)

attribute [local instance] IntegralComparison.Smooth.ProjectivePointTransfer.sourceSeparated
  IntegralComparison.Smooth.ProjectiveSectionClassData.composite_smooth
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_proper IntegralComparison.Smooth.ProjectiveFormTrace.composite_connected

abbrev forms := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g
local instance forms_qc : (forms (g := g) Y).IsQuasicoherent :=
  IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R Y g
local instance pushedForms_qc : ((Scheme.Modules.pushforward f.left).obj
    (forms (g := g) Y)).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f.left
local instance projectiveSeparated : (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).left.IsSeparated := by
  change (Proj (homogeneousSubmodule (Fin (n+2)) R)).IsSeparated
  constructor
  rw [← terminal.comp_from (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))]
  infer_instance

include hbase in
abbrev sourceClosed : IsClosedImmersion s₀ := by
  let : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  exact isClosedImmersion_of_comp_eq_id Y.hom s₀ hbase
abbrev targetClosed := ResidueRecoveryData.section_closed X Y f i s₀ hbase
abbrev targetSection := SectionEvaluationNaturality.image_retraction R Y X f s₀ hbase

local instance sourceBase : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
local instance targetBase : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i.left ⁻¹ᵁ U)
local instance baseTower : IsScalarTower R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
  AffineOpen.DeRhamTrace.sectionTower R Y X f (i.left ⁻¹ᵁ U)

abbrev selectedSection := Integral.FormSectionUnit.unit R Y g (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
  (z • OrdinaryFormScalars.Ordinary.map R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) g
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) 1 (fun a => i.left.app U (D.parameters a))))

abbrev selectedClass := by
  letI := targetClosed X Y f i s₀ hbase
  exact ProjectivePoint.SectionCoordinates.sectionClass X i (s₀ ≫ f.left)
    (targetSection X Y f s₀ hbase) B hB U hU D
    ((Scheme.Modules.pushforward f.left).obj (forms (g := g) Y))
    (selectedSection X Y f i s₀ U hU D z)

abbrev residue_eq := by
  letI := D.finiteVariables
  letI := D.coordinates
  letI := D.coordinateTower
  letI := D.coordinateEtale
  have h := ProjectiveFinite.EtalePointResidue.eq_residue D.dimension X Y f i s₀ hbase B hB U hU
    D.contains hgood D.coordinate D.below_coordinate D.equations D.generates D.regular
    D.conormalBasis D.conormalBasis_apply D.quotientBasis D.parameters D.quotientBasis_apply
    D.point_generates D.point_regular D.ambientBasis D.ambientBasis_apply D.coordinateIndex z hz
  exact h

abbrev selected_fixed := ProjectiveFinite.SelectedFixed.fixed X Y f i s₀ hbase B hB U hU D hgood z hz he

abbrev supportConditions := by
  letI := sourceClosed Y s₀ hbase
  letI := targetClosed X Y f i s₀ hbase
  exact IntegralComparison.Finite.FiberPrincipalSupport.conditions R X Y f i.left s₀ hbase U hU D.contains hgood z hz
    D.parameters (ProjectivePoint.ParameterSource.span X i (s₀ ≫ f.left) g U hU D.toParameterData)

abbrev selectedAffine : IsAffineOpen (Y.left.basicOpen z) := (hgood.1.preimage f.left).basicOpen z
abbrev selectedBelow : Y.left.basicOpen z ≤ (f.left ≫ i.left) ⁻¹ᵁ U := Y.left.basicOpen_le z
abbrev cover := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2))
abbrev coverFull := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n+2))
abbrev coverAffine := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) (σ := Fin (n+2))
abbrev baseMap := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2))

omit [IsNoetherianRing R] [Module.Injective R R] [Nonempty X.left] [Etale f.left]
  [Smooth X.hom] [GeometricallyConnected X.hom] [GeometricallyConnected Y.hom]
  [SmoothOfRelativeDimension g X.hom] in
theorem ordinary_map :
    letI : IsClosedImmersion (s₀ ≫ f.left) := targetClosed X Y f i s₀ hbase
    ResidueRecoveryData.ordinaryMap X Y f i s₀ hbase U hU D =
      PrincipalPoint.Source.Comparison.ordinaryMap f.left i.left
        (baseMap (R := R) (n := n)) (s₀ ≫ f.left) U hU D.contains
        D.equations D.parameters D.generates
        ((KoszulPoint.Ideal.append _ D.equations D.parameters).symm.trans D.point_generates)
        (cover (R := R) (n := n)) (coverFull (R := R) (n := n)) (coverAffine (R := R) (n := n))
        (forms (g := g) Y) (D.codimension+g) (Nat.add_comm D.codimension g) := rfl

abbrev selected_original_recovery := by
  have h := residue_eq X Y f i s₀ hbase B hB U hU D hgood z hz
  have hr := ResidueRecovery.comparison X Y f i s₀ hbase B hB U hU D
  have he : ResidueRecoveryData.residue X Y f i s₀ hbase B hB U hU D =
      selectedClass X Y f i s₀ hbase B hB U hU D z := by
    convert h using 1 <;> (as_aux_lemma => rfl)
  exact (congrArg (ResidueRecoveryData.ordinaryMap X Y f i s₀ hbase U hU D) he).symm.trans hr

abbrev native_recovery := by
  letI := targetClosed X Y f i s₀ hbase
  let hfixed := selected_fixed X Y f i s₀ hbase B hB U hU D hgood z hz he
  have hn := PrincipalPoint.SourceIntrinsicRecovery.Intrinsic.recovery f.left i.left
    (baseMap (R := R) (n := n)) (s₀ ≫ f.left) U hU D.contains D.equations D.parameters D.generates
    ((KoszulPoint.Ideal.append _ D.equations D.parameters).symm.trans D.point_generates)
    (cover (R := R) (n := n)) (coverFull (R := R) (n := n)) (coverAffine (R := R) (n := n))
    (forms (g := g) Y) z (SectionIdealPuncturedCover.outside s₀.ker)
    (supportConditions X Y f i s₀ hbase U hU D hgood z hz)
    (selectedAffine X Y f i U hgood z) (selectedBelow X Y f i U z)
    (selectedClass X Y f i s₀ hbase B hB U hU D z) hfixed
  have hr := selected_original_recovery X Y f i s₀ hbase B hB U hU D hgood z hz
  have hs := congrArg (PrincipalPoint.Source.Comparison.sourceOutput
    (c := D.codimension) (g := g) f.left i.left (baseMap (R := R) (n := n))
    (cover (R := R) (n := n)) (forms (g := g) Y)) hr
  have hm := ConcreteCategory.congr_hom (ordinary_map X Y f i s₀ hbase U hU D)
    (selectedClass X Y f i s₀ hbase B hB U hU D z)
  exact join_equalities hs.symm hn
    (congrArg (PrincipalPoint.Source.Comparison.sourceOutput
      (c := D.codimension) (g := g) f.left i.left (baseMap (R := R) (n := n))
      (cover (R := R) (n := n)) (forms (g := g) Y)) hm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SelectedSourceRecovery
