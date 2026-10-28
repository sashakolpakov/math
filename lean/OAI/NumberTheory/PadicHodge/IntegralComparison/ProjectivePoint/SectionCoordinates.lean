import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueSingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.SingleTopNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SymbolCoordinates

/-! # Section Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionCoordinates

noncomputable section

/-! Multiplication of the actual scalar point residue by any local
section retains its original scalar and single-total sign. This covers
both ordinary top forms and selected finite-source top forms. -/
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

variable (N : X.left.Modules) (ω : Γ(N, i.left ⁻¹ᵁ U))

abbrev sectionMap := Principal.PushforwardSection.map i.left U hU N ω
abbrev sectionDiagram := Principal.SectionPresheaf.modules U hU
  ((Scheme.Modules.pushforward i.left).obj N)

abbrev coordinateIso := Augmented.SingleTopNaturality.coordinates
  (ResidueData.family X i s₀ U hU D) (sectionDiagram X i U hU N)
  D.codimension g (D.codimension+g) (Nat.add_comm D.codimension g)

def sectionClass :
    ((Functor.SingleTotal.bicomplex
      (AugmentedOrdered.CechFunctor.functor (ResidueData.family X i s₀ U hU D))
      (sectionDiagram X i U hU N) D.codimension).total (.up ℕ)).homology (D.codimension+g) :=
  (Supported.CechHomotopyEquivalence.functor
    (ResidueData.family X i s₀ U hU D) (D.codimension+g)).map
    ((single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U))
      (.up ℕ) D.codimension).map (sectionMap X i U hU N ω))
    (ResidueData.residue X i s₀ hbase B hB U hU D)

abbrev symbolValue := PrincipalResidue.SymbolCoordinates.symbolValue i.left U hU
  D.parameters R N ω (ResidueSingleCoordinates.rawValue X i s₀ hbase B hB U hU D)

def topImage : (sectionDiagram X i U hU N).obj
    (op (AugmentedOrdered.CechCoordinates.topObject
      (ResidueData.family X i s₀ U hU D) g (by simp))) :=
  (sectionMap X i U hU N ω).app (op (PrincipalResidue.SymbolCoordinates.top U D.parameters))
    (ResidueSingleCoordinates.coefficient X i s₀ hbase B hB U hU D)

def topSymbol : (sectionDiagram X i U hU N).obj
    (op (AugmentedOrdered.CechCoordinates.topObject
      (ResidueData.family X i s₀ U hU D) g (by simp))) :=
  symbolValue X i s₀ hbase B hB U hU D N ω

def symbolClass : (AugmentedOrdered.Cech.complex
    (ResidueData.family X i s₀ U hU D) (sectionDiagram X i U hU N)).homology g :=
  AugmentedOrdered.CechTopClass.topClass
    (ResidueData.family X i s₀ U hU D) (sectionDiagram X i U hU N)
    g (by simp) (topSymbol X i s₀ hbase B hB U hU D N ω)

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem coefficient_image :
    (sectionMap X i U hU N ω).app (op (PrincipalResidue.SymbolCoordinates.top U D.parameters))
      (ResidueSingleCoordinates.coefficient X i s₀ hbase B hB U hU D) =
    symbolValue X i s₀ hbase B hB U hU D N ω :=
  PrincipalResidue.SymbolCoordinates.symbol i.left U hU D.equations D.generates D.parameters
    R N ω (ResidueSingleCoordinates.rawValue X i s₀ hbase B hB U hU D)

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem top_coefficient : topImage X i s₀ hbase B hB U hU D N ω =
    topSymbol X i s₀ hbase B hB U hU D N ω :=
  coefficient_image X i s₀ hbase B hB U hU D N ω

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem mapped_coordinates :
    (coordinateIso X i s₀ U hU D N).hom
      (sectionClass X i s₀ hbase B hB U hU D N ω) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      AugmentedOrdered.CechTopClass.topClass
        (ResidueData.family X i s₀ U hU D) (sectionDiagram X i U hU N)
        g (by simp)
        (topImage X i s₀ hbase B hB U hU D N ω) :=
  Augmented.SingleTopNaturality.topClass
    (ResidueData.family X i s₀ U hU D)
    D.codimension g (D.codimension+g) (Nat.add_comm D.codimension g)
    (sectionMap X i U hU N ω) (by simp)
    (ResidueData.residue X i s₀ hbase B hB U hU D)
    (ResidueSingleCoordinates.coefficient X i s₀ hbase B hB U hU D)
    (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g)
    (ResidueSingleCoordinates.coordinates X i s₀ hbase B hB U hU D)

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem symbol_coordinates :
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      AugmentedOrdered.CechTopClass.topClass
        (ResidueData.family X i s₀ U hU D) (sectionDiagram X i U hU N)
        g (by simp)
        (topImage X i s₀ hbase B hB U hU D N ω) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      symbolClass X i s₀ hbase B hB U hU D N ω :=
  by
    rw [top_coefficient X i s₀ hbase B hB U hU D N ω]
    rfl

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem coordinates :
    (coordinateIso X i s₀ U hU D N).hom
      (sectionClass X i s₀ hbase B hB U hU D N ω) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      symbolClass X i s₀ hbase B hB U hU D N ω :=
  (mapped_coordinates X i s₀ hbase B hB U hU D N ω).trans
    (symbol_coordinates X i s₀ hbase B hB U hU D N ω)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionCoordinates
