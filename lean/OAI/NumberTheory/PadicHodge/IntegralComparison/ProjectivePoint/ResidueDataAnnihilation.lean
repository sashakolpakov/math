import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueClassCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResidueClassAnnihilation

/-! # Residue Data Annihilation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueDataAnnihilation

noncomputable section

/-! The literal projective residue is annihilated by its actual point
ideal, through its checked original resolution coordinates. -/
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

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem annihilated (a : Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U))
    (ha : a ∈ (s₀ ≫ i.left).ker.ideal ⟨U,hU⟩) :
    a • ResidueData.residue X i s₀ hbase B hB U hU D = 0 := by
  have hk : a ∈ Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)
      (Fin.append D.equations D.parameters) := by
    rw [← KoszulPoint.Ideal.append, D.point_generates]
    exact ha
  have h := Koszul.ResidueClassAnnihilation.annihilated Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)
    (Principal.SectionPresheaf.rings U hU) (ResidueData.family X i s₀ U hU D)
    D.equations D.parameters (PrincipalPoint.Fraction.units U hU D.parameters)
    (ResidueClassData.Coordinates.pointCoordinates X i s₀ B U hU D)
    R (Principal.TerminalScalars.bijective U hU) (n+1)
    (ScalarFraction.pure i.left s₀
      (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU)
    (ScalarFraction.zero i.left s₀
      (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU
      D.equations D.parameters D.point_generates)
    (ScalarFraction.pointQuotient i.left s₀
      (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) U hU D.contains
      D.equations D.parameters D.point_generates)
    (Principal.ClosedKoszulResidue.target i.left U hU)
    (Principal.ClosedKoszulResidue.pullback i.left U hU D.equations D.generates)
    (Principal.ClosedKoszulResidue.annihilated i.left U hU D.equations D.generates)
    (LocalCoordinates.pointAt i.left s₀
      (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU
      D.equations D.parameters D.point_generates D.dimension) a hk
  exact (congrArg (fun y => a • y)
    (ResidueClassCoordinates.residue_coordinates X i s₀ hbase B hB U hU D)).trans h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueDataAnnihilation
