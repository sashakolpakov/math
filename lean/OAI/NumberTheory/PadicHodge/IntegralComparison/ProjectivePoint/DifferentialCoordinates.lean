import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueSingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.SingleTopNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DifferentialSymbolRestriction

/-! # Differential Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.DifferentialCoordinates

noncomputable section

/-! The actual projective point adjunction has the same fractional
ordinary top-form coordinate as its scalar residue, with the original
interchange sign and coefficient unchanged. -/
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

abbrev coefficientMap := Principal.DifferentialSymbol.map R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) i U hU g
  (fun j => i.left.app U (D.parameters j))

abbrev formDiagram := Principal.SectionPresheaf.modules U hU
  ((Scheme.Modules.pushforward i.left).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g))

abbrev coordinateIso := Augmented.SingleTopNaturality.coordinates
  (ResidueData.family X i s₀ U hU D) (formDiagram (g := g) X i U hU)
  D.codimension g (D.codimension+g) (Nat.add_comm D.codimension g)

abbrev symbolValue := Principal.DifferentialSymbolRestriction.sourceValue R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1))
  i U hU D.parameters (ResidueSingleCoordinates.rawValue X i s₀ hbase B hB U hU D)

abbrev symbolClass := AugmentedOrdered.CechTopClass.topClass
  (ResidueData.family X i s₀ U hU D) (formDiagram (g := g) X i U hU)
  g (by simp) (symbolValue X i s₀ hbase B hB U hU D)

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem coefficient_image :
    (coefficientMap X i s₀ U hU D).app
      (op (PrincipalResidue.SymbolCoordinates.top U D.parameters))
      (ResidueSingleCoordinates.coefficient X i s₀ hbase B hB U hU D) =
    symbolValue X i s₀ hbase B hB U hU D := by
  exact congrArg ((coefficientMap X i s₀ U hU D).app
    (op (PrincipalResidue.SymbolCoordinates.top U D.parameters)))
    (PrincipalResidue.SymbolCoordinates.value_eq i.left U hU D.equations D.generates
      D.parameters R (ResidueSingleCoordinates.rawValue X i s₀ hbase B hB U hU D))

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem differential_coordinates :
    (coordinateIso X i s₀ U hU D).hom
      (ResidueData.differential X i s₀ hbase B hB U hU D) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      symbolClass X i s₀ hbase B hB U hU D := by
  have h := SectionCoordinates.coordinates X i s₀ hbase B hB U hU D
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
    (Principal.DifferentialSymbol.generator R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) i U g
      (fun j => i.left.app U (D.parameters j)))
  change (coordinateIso X i s₀ U hU D).hom
      (ResidueData.differential X i s₀ hbase B hB U hU D) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      symbolClass X i s₀ hbase B hB U hU D at h
  exact h

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [GeometricallyConnected X.hom] in
theorem form_coordinates :
    (coordinateIso X i s₀ U hU D).hom
      (ResidueData.form X i s₀ hbase B hB U hU D) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      symbolClass X i s₀ hbase B hB U hU D := by
  have h : ResidueData.differential X i s₀ hbase B hB U hU D =
      ResidueData.form X i s₀ hbase B hB U hU D :=
    ResidueData.comparison X i s₀ hbase B hB U hU D
  exact (congrArg (fun x => (coordinateIso X i s₀ U hU D).hom x) h).symm.trans
    (differential_coordinates X i s₀ hbase B hB U hU D)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.DifferentialCoordinates
