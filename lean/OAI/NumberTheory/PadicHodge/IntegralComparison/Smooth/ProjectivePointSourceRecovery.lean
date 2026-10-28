import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveResidueRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.CanonicalSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SameSupportIntrinsic
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SupportConditions
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormSourceCoordinates

/-! # Projective Point Source Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectivePointSourceRecovery

noncomputable section

/-! The original smooth point section recovers through the genuine
native principal comparison on any affine neighborhood of its support. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem join_equalities {A : Type*} {a b c d : A}
    (hab : a = b) (hcd : c = d) (hbc : b = c) : a = d :=
  hab.trans (hbc.trans hcd)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
variable {R : Type} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) [Nonempty X.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [SmoothOfRelativeDimension g X.hom]
  (s₀ : Spec (CommRingCat.of R) ⟶ X.left) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ X.hom = 𝟙 _)
  (B : ℕ) (hB : n+2≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i s₀ g U hU)
attribute [local instance] ProjectivePointTransfer.sourceSeparated
  ProjectiveSectionClassData.composite_smooth
  ProjectiveFormTrace.composite_proper ProjectiveFormTrace.composite_connected
  ProjectiveFormTrace.composite_dimension
  ProjectivePoint.Survivor.coefficient_qc ProjectivePoint.Survivor.coefficient_finite

local instance projectiveSeparated : (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).left.IsSeparated := by
  change (Proj (homogeneousSubmodule (Fin (n+2)) R)).IsSeparated
  constructor
  rw [← terminal.comp_from (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))]
  infer_instance

abbrev form := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
local instance form_qc : (form (g := g) X).IsQuasicoherent :=
  FormCoherence.Integral.quasicoherent R X g
abbrev cover := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2))
abbrev coverFull := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n+2))
abbrev coverAffine := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) (σ := Fin (n+2))
abbrev baseMap := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2))
abbrev globalCover := PrincipalPoint.PulledIntegerRefinement.global (𝟙 X.left) i.left
  (cover (R := R) (n := n))
abbrev globalCoverFull := PrincipalPoint.PulledIntegerRefinement.global_cover (𝟙 X.left) i.left
  (cover (R := R) (n := n)) (coverFull (R := R) (n := n))
abbrev globalCoverAffine := PrincipalPoint.PulledIntegerRefinement.global_affine (𝟙 X.left) i.left
  (cover (R := R) (n := n)) (coverAffine (R := R) (n := n))

def sourceOutput := PrincipalPoint.Source.Comparison.sourceOutput
  (c := D.codimension) (g := g) (𝟙 X.left) i.left (baseMap (R := R) (n := n))
  (cover (R := R) (n := n)) (form (g := g) X)

abbrev ordinary_comparison := PrincipalPoint.Source.Comparison.comparison_apply
  (𝟙 X.left) i.left (baseMap (R := R) (n := n)) s₀ U hU D.contains
  D.equations D.parameters D.generates
  ((KoszulPoint.Ideal.append _ D.equations D.parameters).symm.trans D.point_generates)
  (cover (R := R) (n := n)) (coverFull (R := R) (n := n)) (coverAffine (R := R) (n := n))
  (form (g := g) X) (ProjectivePoint.ResidueData.form X i s₀ hbase B hB U hU D)

omit [IsNoetherianRing R] [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R]
  [Nonempty X.left] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem ordinary_map : ProjectiveResidueRecoveryData.ordinaryMap X i s₀ U hU D =
    PrincipalPoint.Source.Comparison.ordinaryMap
      (𝟙 X.left) i.left (baseMap (R := R) (n := n)) s₀ U hU D.contains
      D.equations D.parameters D.generates
      ((KoszulPoint.Ideal.append _ D.equations D.parameters).symm.trans D.point_generates)
      (cover (R := R) (n := n)) (coverFull (R := R) (n := n)) (coverAffine (R := R) (n := n))
      (form (g := g) X) (D.codimension+g) (Nat.add_comm D.codimension g) := rfl

abbrev recovery := by
  have ho := ordinary_comparison X i s₀ hbase B hB U hU D
  have hr := ProjectiveResidueRecovery.comparison X i s₀ hbase B hB U hU D
  have hs := congrArg (sourceOutput X i s₀ U hU D) hr.symm
  have hm := ConcreteCategory.congr_hom (ordinary_map X i s₀ U hU D)
    (ProjectivePoint.ResidueData.form X i s₀ hbase B hB U hU D)
  exact join_equalities hs ho (congrArg (sourceOutput X i s₀ U hU D) hm)

variable (V : X.left.Opens) (hV : IsAffineOpen V) (hVU : V ≤ i.left ⁻¹ᵁ U)
  (hcontains : ⊤ ≤ s₀ ⁻¹ᵁ V)

abbrev conditions := PrincipalPoint.SupportConditions.ProjectiveParameter.conditions X i s₀ g U hU D.toParameterData
  V hV hVU hcontains
abbrev outside := SectionIdealPuncturedCover.outside s₀.ker

abbrev canonical_recovery := by
  have h := recovery X i s₀ hbase B hB U hU D
  have hc := PrincipalPoint.CanonicalSource.sourceComparison_eq (𝟙 X.left) i.left s₀ U hU D.contains
    D.equations D.parameters D.generates
    ((KoszulPoint.Ideal.append _ D.equations D.parameters).symm.trans D.point_generates)
    (cover (R := R) (n := n)) (coverFull (R := R) (n := n)) (coverAffine (R := R) (n := n))
    (form (g := g) X) (PrincipalSource.OpenReindex.geometricOpens i.left U hU V)
    (outside X s₀) (conditions X i s₀ U hU D V hV hVU hcontains)
  rw [hc] at h
  exact h

abbrev native_recovery := by
  have hc := canonical_recovery X i s₀ hbase B hB U hU D V hV hVU hcontains
  have hn := Principal.SameSupportIntrinsic.Intrinsic.recovery i.left U hU V hV hVU D.parameters
    (outside X s₀) (conditions X i s₀ U hU D V hV hVU hcontains) (form (g := g) X)
    D.codimension (g+D.codimension) (globalCover X i)
    (globalCoverFull X i) (globalCoverAffine X i)
    (PrincipalSource.ClassCoordinates.wideClass (𝟙 X.left) i.left U hU (form (g := g) X)
      D.parameters D.codimension (ProjectivePoint.ResidueData.form X i s₀ hbase B hB U hU D))
  exact hc.trans hn

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectivePointSourceRecovery
