import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.DifferentialCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ClassCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdentityPushforwardModule

/-! # Form Source Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormSourceCoordinates

noncomputable section

/-! The original differential point residue in source-open coordinates,
with the original ambient scalar and codimension sign unchanged. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
variable {R : Type} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) [Nonempty X.left]
  (i : X ⟶ IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [SmoothOfRelativeDimension g X.hom]
  (s₀ : Spec (CommRingCat.of R) ⟶ X.left) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ X.hom = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i s₀ g U hU)
attribute [local instance] IntegralComparison.Smooth.ProjectivePointTransfer.sourceSeparated
  IntegralComparison.Smooth.ProjectiveSectionClassData.composite_smooth
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_proper
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_connected

abbrev form := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
abbrev symbol := ProjectivePoint.DifferentialCoordinates.symbolValue X i s₀ hbase B hB U hU D

variable (V : X.left.Opens) (hV : IsAffineOpen V) (hVU : V ≤ i.left ⁻¹ᵁ U)

def nativeClass := PrincipalSource.ClassCoordinates.nativeClass (𝟙 X.left) i.left U hU
  (form (g := g) X) D.parameters D.codimension V hV (by simpa only [Category.id_comp] using hVU)
  (ProjectivePoint.ResidueData.form X i s₀ hbase B hB U hU D)

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [GeometricallyConnected X.hom] in
theorem coordinates :
    (PrincipalSource.IntrinsicCoordinates.Intrinsic.nativeCoordinates i.left U V hV hVU
      (form (g := g) X) D.parameters D.codimension).hom
      (nativeClass X i s₀ hbase B hB U hU D V hV hVU) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      homologyMap (PrincipalSource.OpenTopClass.complexMap i.left U hU V hV hVU
        (form (g := g) X) D.parameters) g
        (AugmentedCech.TopClassMap.map (PrincipalPoint.Fraction.family U D.parameters)
          (PrincipalSource.OpenTopClass.source i.left U hU (form (g := g) X)) g (by simp)
          (symbol X i s₀ hbase B hB U hU D)) := by
  have h := PrincipalSource.ClassCoordinates.coordinates (𝟙 X.left) i.left U hU
    (form (g := g) X) D.parameters D.codimension V hV
    (by simpa only [Category.id_comp] using hVU)
    (ProjectivePoint.ResidueData.form X i s₀ hbase B hB U hU D)
    (symbol X i s₀ hbase B hB U hU D)
    (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g)
    (ProjectivePoint.DifferentialCoordinates.form_coordinates X i s₀ hbase B hB U hU D)
  convert h using 1 <;> rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormSourceCoordinates
