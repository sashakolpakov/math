import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormSourceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelPrincipalSheaf

/-! # Form Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormFraction

noncomputable section

/-! The actual differential point residue enters the native fraction
map with its original codimension sign and any lift of its actual scalar. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  [IsNoetherianRing (Truncated.Witt.Ring p k n)]
  [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)]
  [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] {d g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Nonempty X.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom]
  (i : X ⟶ IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) [IsClosedImmersion i.left]
  (s₀ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X.left) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ X.hom = 𝟙 _) (B : ℕ) (hB : d+2 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space (Truncated.Witt.Ring p k n) (d+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i s₀ g U hU)
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (V : X.left.affineOpens) (hVU : V.val ≤ i.left ⁻¹ᵁ U)

attribute [local instance] IntegralComparison.Smooth.ProjectivePointTransfer.sourceSeparated
  IntegralComparison.Smooth.ProjectiveSectionClassData.composite_smooth
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_proper IntegralComparison.Smooth.ProjectiveFormTrace.composite_connected

abbrev rawValue := ProjectivePoint.ResidueSingleCoordinates.rawValue X i s₀ hbase B hB U hU D
abbrev nativeClass := FormSourceCoordinates.nativeClass X i s₀ hbase B hB U hU D
  V.val V.property hVU

variable (r : WittVector p k) (hr : Truncated.Witt.quotient p k n r = rawValue p k n X i s₀ hbase B hB U hU D)

include hr in
omit [Fintype k] [CharP k p] [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem symbol : FormSourceCoordinates.symbol X i s₀ hbase B hB U hU D =
    Principal.DifferentialSymbolRestriction.sourceValue (Truncated.Witt.Ring p k n) X
      (IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) i U hU D.parameters
      (Truncated.Witt.quotient p k n r) :=
  congrArg (Principal.DifferentialSymbolRestriction.sourceValue (Truncated.Witt.Ring p k n)
    X (IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) i U hU D.parameters) hr.symm

include hr in
omit [IsSeparated Y.hom] in
omit [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [GeometricallyConnected X.hom] in
theorem coordinates :
    (PrincipalSource.IntrinsicCoordinates.Intrinsic.nativeCoordinates i.left U V.val V.property hVU
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)
      D.parameters D.codimension).hom (nativeClass p k n X i s₀ hbase B hB U hU D V hVU) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      TruncatedModel.OrdinaryFractionRestriction.Ordinary.targetClass p k n X Y f hp
        (IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) i U V hVU g D.parameters r := by
  have hc := FormSourceCoordinates.coordinates X i s₀ hbase B hB U hU D V.val V.property hVU
  erw [symbol p k n X i s₀ hbase B hB U hU D r hr] at hc
  have ht := TruncatedModel.OrdinaryFractionRestriction.Ordinary.topClass p k n X Y f hp
    (IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) i U hU V hVU g D.parameters r
  exact hc.trans (congrArg (fun y => ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g • y) ht)

include hr in
omit [IsSeparated Y.hom] in
omit [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [GeometricallyConnected X.hom] in
theorem native_input :
    TruncatedModel.ModelPrincipalSheaf.input p k n X (IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1))
      i U V hVU g D.codimension D.parameters
      (ULift.up.{2,1} (ULift.up.{1,0} (nativeClass p k n X i s₀ hbase B hB U hU D V hVU))) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      TruncatedModel.ModelPrincipalFraction.input p k n X Y f hp V g
        (TruncatedModel.ResidueFraction.localParameters p k n X
          (IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) i U V hVU g D.parameters) D.codimension r := by
  exact TruncatedModel.ModelPrincipalSheaf.weighted p k n X Y f hp
    (IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) i U V hVU g D.codimension D.parameters
    (nativeClass p k n X i s₀ hbase B hB U hU D V hVU)
    (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g) r
    (coordinates p k n X i s₀ hbase B hB U hU D Y f hp V hVU r hr)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormFraction
