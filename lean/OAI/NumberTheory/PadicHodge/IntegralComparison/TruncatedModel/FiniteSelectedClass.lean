import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SelectedSourceRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SelectedFractionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SelectedFractionRestriction

/-! # Finite Selected Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FiniteSelectedClass

noncomputable section

/-! The selected finite-residue class is the literal selected native
fraction class; the original scalar residue and numerator are unchanged. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  [IsNoetherianRing (Truncated.Witt.Ring p k n)]
  [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)]
  [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)]
  {d g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable (X Y : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Nonempty X.left]
  (f : Y ⟶ X) [IsFinite f.left] [Etale f.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom]
  [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] [SmoothOfRelativeDimension g Y.hom]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) [IsClosedImmersion i.left]
  (s₀ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ Y.left)
  (hbase : s₀ ≫ Y.hom = 𝟙 _) (B : ℕ) (hB : d+2 ≤ B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space (Truncated.Witt.Ring p k n) (d+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i (s₀ ≫ f.left) g U hU)
  (z : Finite.FlatCoefficientSections.coefficientRing f.left i.left U)

attribute [local instance] IntegralComparison.Smooth.ProjectivePointTransfer.sourceSeparated
  IntegralComparison.Smooth.ProjectiveSectionClassData.composite_smooth
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_proper IntegralComparison.Smooth.ProjectiveFormTrace.composite_connected

local instance targetBase : Algebra (Truncated.Witt.Ring p k n) (Finite.FlatCoefficientSections.quotientRing i.left U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) X (i.left ⁻¹ᵁ U)
local instance sourceBase : Algebra (Truncated.Witt.Ring p k n) (Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
local instance baseTower : IsScalarTower (Truncated.Witt.Ring p k n) (Finite.FlatCoefficientSections.quotientRing i.left U)
    (Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
  AffineOpen.DeRhamTrace.sectionTower (Truncated.Witt.Ring p k n) Y X f (i.left ⁻¹ᵁ U)

omit [Fintype k] [CharP k p] [IsNoetherianRing (Truncated.Witt.Ring p k n)] [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)] [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] [SmoothOfRelativeDimension g Y.hom] [IsClosedImmersion (Over.Hom.left i)] in
theorem section_eq : FiniteEtale.SelectedSourceRecovery.selectedSection X Y f i s₀ U hU D z =
    SelectedFractionRestriction.selectedSection p k n Y
      (Projective.IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) (f ≫ i) U g D.parameters z := by
  let : Algebra (Finite.FlatCoefficientSections.quotientRing i.left U) Γ(Y.left,(f ≫ i).left ⁻¹ᵁ U) :=
    Finite.FlatCoefficientSections.coefficientAlgebra f.left i.left U
  let : IsScalarTower (Truncated.Witt.Ring p k n) (Finite.FlatCoefficientSections.quotientRing i.left U)
      Γ(Y.left,(f ≫ i).left ⁻¹ᵁ U) :=
    AffineOpen.DeRhamTrace.sectionTower (Truncated.Witt.Ring p k n) Y X f (i.left ⁻¹ᵁ U)
  exact SelectedFractionRestriction.mapped_section p k n Y
    (Projective.IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) (f ≫ i) U g D.parameters z
    (Finite.FlatCoefficientSections.quotientRing i.left U) (fun j => i.left.app U (D.parameters j)) (fun _ => rfl)

abbrev class_eq := by
  letI := FiniteEtale.SelectedSourceRecovery.targetClosed X Y f i s₀ hbase
  exact congrArg (fun ω => ProjectivePoint.SectionCoordinates.sectionClass X i (s₀ ≫ f.left)
    (SectionEvaluationNaturality.image_retraction (Truncated.Witt.Ring p k n) Y X f s₀ hbase)
    B hB U hU D ((Scheme.Modules.pushforward f.left).obj
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) Y g)) ω)
    (section_eq p k n X Y f i s₀ U hU D z)

variable (V : Y.left.affineOpens) (hVU : V.val ≤ (f ≫ i).left ⁻¹ᵁ U)

abbrev native_eq := by
  letI := FiniteEtale.SelectedSourceRecovery.targetClosed X Y f i s₀ hbase
  exact congrArg (fun ω => ProjectivePoint.SectionSourceCoordinates.nativeClass X i (s₀ ≫ f.left)
    (SectionEvaluationNaturality.image_retraction (Truncated.Witt.Ring p k n) Y X f s₀ hbase)
    B hB U hU D f.left (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) Y g)
    ω V.val V.property hVU) (section_eq p k n X Y f i s₀ U hU D z)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FiniteSelectedClass
