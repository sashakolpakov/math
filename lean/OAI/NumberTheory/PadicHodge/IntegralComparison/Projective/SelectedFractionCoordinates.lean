import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionSourceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SelectedFractionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SymbolPushforward

/-! # Selected Fraction Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SelectedFractionCoordinates

noncomputable section

/-! The selected projective section class has the exact native local
fraction coordinate, preserving its original scalar and codimension sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

abbrev baseRing (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (n : ℕ) := Truncated.Witt.Ring p k n

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  [IsNoetherianRing (baseRing p k n)] [Module.Injective (baseRing p k n) (baseRing p k n)]
  [IsArtinianRing (baseRing p k n)] [IsLocalRing (baseRing p k n)] {d g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of (baseRing p k n)))) [Nonempty X.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom]
  (i : X ⟶ IntrinsicOverlap.Intrinsic.model (baseRing p k n) (d+1)) [IsClosedImmersion i.left]
  (s₀ : Spec (CommRingCat.of (baseRing p k n)) ⟶ X.left) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ X.hom = 𝟙 _) (B : ℕ) (hB : d+2 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space (baseRing p k n) (d+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i s₀ g U hU)
  (Y : Over (Spec (CommRingCat.of (baseRing p k n))))
  [Smooth Y.hom] [IsProper Y.hom] [Y.left.IsSeparated] [SmoothOfRelativeDimension g Y.hom]
  (f : Y ⟶ X)
  (Z : Over (Spec (CommRingCat.of k))) [IsSeparated Z.hom]
  (j : Z.left ⟶ Y.left)
  (hp : IsPullback j Z.hom Y.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (V : Y.left.affineOpens) (hVU : V.val ≤ (f ≫ i).left ⁻¹ᵁ U)
  (z : Γ(Y.left,(f ≫ i).left ⁻¹ᵁ U))

attribute [local instance] IntegralComparison.Smooth.ProjectivePointTransfer.sourceSeparated
  IntegralComparison.Smooth.ProjectiveSectionClassData.composite_smooth
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_proper IntegralComparison.Smooth.ProjectiveFormTrace.composite_connected

local instance ambientAlgebra : Algebra (baseRing p k n) Γ(IntrinsicOverlap.Intrinsic.space (baseRing p k n) (d+1), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (baseRing p k n) (IntrinsicOverlap.Intrinsic.model (baseRing p k n) (d+1)) U

abbrev form := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (baseRing p k n) Y g
abbrev selectedSection := TruncatedModel.SelectedFractionRestriction.selectedSection
  p k n Y (IntrinsicOverlap.Intrinsic.model (baseRing p k n) (d+1)) (f ≫ i) U g D.parameters z
abbrev rawValue := ProjectivePoint.ResidueSingleCoordinates.rawValue X i s₀ hbase B hB U hU D
abbrev nativeClass := ProjectivePoint.SectionSourceCoordinates.nativeClass X i s₀ hbase B hB U hU D
  f.left (form p k n Y (g := g)) (selectedSection p k n X i s₀ U hU D Y f z) V.val V.property hVU

variable (r : WittVector p k) (hr : Truncated.Witt.quotient p k n r = rawValue p k n X i s₀ hbase B hB U hU D)

include hr in
omit [IsArtinianRing (baseRing p k n)] [IsLocalRing (baseRing p k n)] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] [Smooth Y.hom] [IsProper Y.hom] [Y.left.IsSeparated] [SmoothOfRelativeDimension g Y.hom] in
theorem symbol :
    ProjectivePoint.SectionSourceCoordinates.symbol X i s₀ hbase B hB U hU D f.left
      (form p k n Y (g := g)) (selectedSection p k n X i s₀ U hU D Y f z) =
    PrincipalResidue.SymbolCoordinates.symbolValue (f ≫ i).left U hU D.parameters
      (baseRing p k n) (form p k n Y (g := g)) (selectedSection p k n X i s₀ U hU D Y f z)
      (Truncated.Witt.quotient p k n r) := by
  have hs := Principal.SymbolPushforward.symbol f.left i.left U hU D.parameters
    (baseRing p k n) (form p k n Y (g := g)) (selectedSection p k n X i s₀ U hU D Y f z)
    (rawValue p k n X i s₀ hbase B hB U hU D)
  have he := congrArg (PrincipalResidue.SymbolCoordinates.symbolValue (f ≫ i).left
    U hU D.parameters (baseRing p k n) (form p k n Y (g := g))
    (selectedSection p k n X i s₀ U hU D Y f z)) hr.symm
  exact hs.trans he

variable {κ : Type} [CommRing κ] (η : Γ(Y.left,V.val) →+* κ)
  (hk : Koszul.OrientedTopCohomology.ideal Γ(Y.left,V.val)
    (PrincipalResidue.ResidueRestriction.parameters (f ≫ i).left U V.val hVU D.parameters) = RingHom.ker η)
  (hz : η (Y.left.presheaf.map (homOfLE hVU).op z) = 1)

include hk hz hr in
omit [IsSeparated Z.hom] in
omit [IsArtinianRing (baseRing p k n)] [IsLocalRing (baseRing p k n)] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] [IsProper Y.hom] [Y.left.IsSeparated] [SmoothOfRelativeDimension g Y.hom] in
theorem coordinates :
    (PrincipalSource.IntrinsicCoordinates.Intrinsic.nativeCoordinates (f ≫ i).left U V.val V.property hVU
      (form p k n Y (g := g)) D.parameters D.codimension).hom
      (nativeClass p k n X i s₀ hbase B hB U hU D Y f V hVU z) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      TruncatedModel.OrdinaryFractionRestriction.Ordinary.targetClass p k n Y Z j hp
        (IntrinsicOverlap.Intrinsic.model (baseRing p k n) (d+1)) (f ≫ i) U V hVU g D.parameters r := by
  have hc := ProjectivePoint.SectionSourceCoordinates.coordinates X i s₀ hbase B hB U hU D
    f.left (form p k n Y (g := g)) (selectedSection p k n X i s₀ U hU D Y f z) V.val V.property hVU
  erw [symbol p k n X i s₀ hbase B hB U hU D Y f z r hr] at hc
  have ht := TruncatedModel.SelectedFractionRestriction.restriction p k n Y Z j hp
    (IntrinsicOverlap.Intrinsic.model (baseRing p k n) (d+1)) (f ≫ i) U hU V hVU g D.parameters z η hk hz r
  exact hc.trans (congrArg (fun y => ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g • y) ht)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SelectedFractionCoordinates
