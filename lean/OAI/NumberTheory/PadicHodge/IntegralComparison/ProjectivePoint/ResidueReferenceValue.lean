import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueCochainApply

/-! # Residue Reference Value -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueReferenceValue.Reference

noncomputable section

/-! The exact scalar expression in the original point comparison is
the residue of the original point class, before applying a coefficient
weight or a differential-symbol map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private abbrev equalityLeft {A : Sort*} {a b : A} (_ : a = b) : A := a

private theorem normalize {A B : Type*} {f g : A → B} {x : A} {y : B}
    (hfg : ∀ a, f a = g a) (hgy : g x = y) : f x = y :=
  (hfg x).trans hgy

private theorem replace_lhs {A : Sort*} {a b c : A} (h : a = b) (hc : c = a) : c = b :=
  hc.trans h

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
  ResidueClassData.Coordinates.sectionAlgebra
  ResidueClassData.Coordinates.scalar_qc
  ResidueClassData.Coordinates.scalar_finite
  ResidueClassData.Coordinates.line_qc

def value : ResidueMapData.Coordinates.output X i s₀ U hU D :=
  equalityLeft (ResidueClass.fixedPoint i.left s₀
    (IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s₀ hbase) B hB U hU D.contains
    D.coordinate D.below_coordinate (ResidueData.frame X i s₀ U hU D)
    D.equations D.parameters D.generates D.point_generates D.regular D.point_regular D.dimension)

attribute [local irreducible] HomologicalComplex.homology

abbrev normalized := normalize
  (ResidueCochainApply.comparison X i s₀ B U hU D)
  (ResidueNormalization.comparison X i s₀ hbase B hB U hU D)

omit [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem comparison : value X i s₀ hbase B hB U hU D =
    ResidueData.residue X i s₀ hbase B hB U hU D := by
  exact replace_lhs (normalized X i s₀ hbase B hB U hU D) (by as_aux_lemma => rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueReferenceValue.Reference
