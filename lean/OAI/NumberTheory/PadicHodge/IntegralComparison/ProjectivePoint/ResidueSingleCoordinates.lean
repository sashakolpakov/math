import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueData
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedResidueSingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueClassCoordinates

/-! # Residue Single Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueSingleCoordinates

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

local instance sectionAlgebra : Algebra R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) U

abbrev rawValue : R :=
  ScalarCoordinates.rawValue i.left s₀
    (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU D.contains
    D.coordinate D.below_coordinate (ResidueData.frame X i s₀ U hU D)
    D.equations D.parameters D.point_generates D.point_regular
    (LocalCoordinates.pointAt i.left s₀
      (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU
      D.equations D.parameters D.point_generates D.dimension)

abbrev coefficient :=
  Koszul.RefinedResidueSingleCoordinates.scalarValue Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)
    (Principal.SectionPresheaf.rings U hU) (ResidueData.family X i s₀ U hU D)
    D.parameters (PrincipalPoint.Fraction.units U hU D.parameters)
    (Principal.ClosedKoszulResidue.target i.left U hU)
    (Principal.ClosedKoszulResidue.pullback i.left U hU D.equations D.generates)
    R (rawValue X i s₀ hbase B hB U hU D)

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
private theorem raw_coordinates :
    (Functor.SingleTotal.homologyIso
      (AugmentedOrdered.CechFunctor.functor (ResidueData.family X i s₀ U hU D))
      (Principal.ClosedKoszulResidue.target i.left U hU) D.codimension g).hom
      ((eqToHom (congrArg
        (fun j => ((AugmentedOrdered.CechFunctor.bicomplex
          (ResidueData.family X i s₀ U hU D)
          (Koszul.CoefficientResidueClass.residueTarget Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)
            (c := D.codimension) (Principal.ClosedKoszulResidue.target i.left U hU))).total
          (.up ℕ)).homology j) (Nat.add_comm D.codimension g)))
        (ResidueClassData.Coordinates.rawResidue X i s₀ hbase B hB U hU D)) =
      ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
        AugmentedOrdered.CechTopClass.topClass
          (ResidueData.family X i s₀ U hU D)
          (Principal.ClosedKoszulResidue.target i.left U hU) g (by simp)
          (coefficient X i s₀ hbase B hB U hU D) := by
  exact Koszul.RefinedResidueSingleCoordinates.coordinates Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)
    (Principal.SectionPresheaf.rings U hU) (ResidueData.family X i s₀ U hU D)
    D.equations D.parameters (PrincipalPoint.Fraction.units U hU D.parameters)
    (Principal.ClosedKoszulResidue.target i.left U hU)
    (Principal.ClosedKoszulResidue.pullback i.left U hU D.equations D.generates) R
    (ResidueClassData.Coordinates.pointCoordinates X i s₀ B U hU D)
    (Principal.TerminalScalars.bijective U hU) (n+1)
    (ScalarFraction.pure i.left s₀
      (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU)
    (ScalarFraction.zero i.left s₀
      (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU
      D.equations D.parameters D.point_generates)
    (ScalarFraction.pointQuotient i.left s₀
      (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) U hU D.contains
      D.equations D.parameters D.point_generates) _

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem coordinates :
    (Functor.SingleTotal.homologyIso
      (AugmentedOrdered.CechFunctor.functor (ResidueData.family X i s₀ U hU D))
      (Principal.ClosedKoszulResidue.target i.left U hU) D.codimension g).hom
      ((eqToHom (congrArg
        (fun j => ((AugmentedOrdered.CechFunctor.bicomplex
          (ResidueData.family X i s₀ U hU D)
          (Koszul.CoefficientResidueClass.residueTarget Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)
            (c := D.codimension) (Principal.ClosedKoszulResidue.target i.left U hU))).total
          (.up ℕ)).homology j) (Nat.add_comm D.codimension g)))
        (ResidueData.residue X i s₀ hbase B hB U hU D)) =
      ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
        AugmentedOrdered.CechTopClass.topClass
          (ResidueData.family X i s₀ U hU D)
          (Principal.ClosedKoszulResidue.target i.left U hU) g (by simp)
          (coefficient X i s₀ hbase B hB U hU D) := by
  rw [ResidueClassCoordinates.residue_coordinates]
  exact raw_coordinates X i s₀ hbase B hB U hU D

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueSingleCoordinates
