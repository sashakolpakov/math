import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ClassCoordinates

/-! # Section Source Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionSourceCoordinates

noncomputable section

/-! The actual projective section residue in the native source-open
single coordinates, with its original scalar and codimension sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
variable {R : Type} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
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

variable {Y : Scheme} (f : Y ⟶ X.left) (N : Y.Modules)
  (ω : Γ(N,f ⁻¹ᵁ (i.left ⁻¹ᵁ U)))
  (V : Y.Opens) (hV : IsAffineOpen V) (hVU : V ≤ (f ≫ i.left) ⁻¹ᵁ U)

abbrev sectionClass := SectionCoordinates.sectionClass X i s₀ hbase B hB U hU D
  ((Scheme.Modules.pushforward f).obj N) ω

abbrev symbol := SectionCoordinates.symbolValue X i s₀ hbase B hB U hU D
  ((Scheme.Modules.pushforward f).obj N) ω

def nativeClass := PrincipalSource.ClassCoordinates.nativeClass f i.left U hU N D.parameters
  D.codimension V hV hVU (sectionClass X i s₀ hbase B hB U hU D f N ω)

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem coordinates :
    (PrincipalSource.IntrinsicCoordinates.Intrinsic.nativeCoordinates (f ≫ i.left) U V hV hVU N D.parameters
      D.codimension).hom (nativeClass X i s₀ hbase B hB U hU D f N ω V hV hVU) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      homologyMap (PrincipalSource.OpenTopClass.complexMap (f ≫ i.left) U hU V hV hVU N D.parameters) g
        (AugmentedCech.TopClassMap.map (PrincipalPoint.Fraction.family U D.parameters)
          (PrincipalSource.OpenTopClass.source (f ≫ i.left) U hU N) g (by simp)
          (symbol X i s₀ hbase B hB U hU D f N ω)) := by
  apply PrincipalSource.ClassCoordinates.coordinates f i.left U hU N D.parameters D.codimension
    V hV hVU (sectionClass X i s₀ hbase B hB U hU D f N ω)
    (symbol X i s₀ hbase B hB U hU D f N ω)
  exact SectionCoordinates.coordinates X i s₀ hbase B hB U hU D
    ((Scheme.Modules.pushforward f).obj N) ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionSourceCoordinates
