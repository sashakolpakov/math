import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectivePureTrace

/-! # Projective Form Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveFormTrace

noncomputable section

/-! The actual top differential-form sheaf inherits the normalized
Serre trace through the proved global adjunction. For a pointed smooth
proper geometrically connected family over the stated Artinian base,
this trace is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing
open OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) [Nonempty X.left]
  (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) [IsClosedImmersion f.left]
  (B : ℕ) (hB : n + 2 ≤ B) (g : ℕ)
  [SmoothOfRelativeDimension g X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]

local instance composite_dimension : SmoothOfRelativeDimension g
    (f.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))) := by
  change SmoothOfRelativeDimension g (f.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w f]
  infer_instance

local instance composite_proper : IsProper
    (f.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))) := by
  change IsProper (f.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w f]
  infer_instance

local instance composite_connected : GeometricallyConnected
    (f.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))) := by
  change GeometricallyConnected (f.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w f]
  infer_instance

include X f in
omit [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R] [IsProper X.hom] [GeometricallyConnected X.hom] in
private theorem dimension_le : g ≤ n + 1 := by
  have h := ClosedDimension.projective f.left g
  simp only [Fintype.card_fin] at h
  omega

def adjunctionIso :
    (ProjectiveRefinement.Serre.fixedDual
      (Projective.ClosedImmersionPurity.directImage f.left) B n (Fintype.card_fin (n + 2))).homology
        (n + 1 - g) ≅
      Intrinsic.ClosedFormSections.directImage R X (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) f g := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  exact Projective.AdjunctionGlobal.iso X f g
    (NegativeTwistResidueNaturality.topChart.{u} (n + 1) (Fintype.card_fin (n + 2))) B hB (dimension_le X f g)

abbrev cohomology : AddCommGrpCat.{u} :=
  (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g).obj
    (Intrinsic.ClosedFormSections.directImage R X (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) f g)

def trace : cohomology X f g ⟶ AddCommGrpCat.of (Projective.TopTracePairing.coefficientRing R) :=
  (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g).map
      (adjunctionIso X f B hB g).inv ≫
    ProjectivePureTrace.trace f.left B n (Fintype.card_fin (n + 2)) hB g

variable (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)

include hs in
omit [IsNoetherianRing R] [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R] [Nonempty ↥X.left] [IsClosedImmersion (Over.Hom.left f)] [IsProper X.hom] [GeometricallyConnected X.hom] in
private theorem section_eq :
    s ≫ (f.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))) = 𝟙 _ := by
  change s ≫ (f.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom) = 𝟙 _
  rw [Over.w f]
  exact hs

def traceIso : cohomology X f g ≅ AddCommGrpCat.of (Projective.TopTracePairing.coefficientRing R) :=
  ((ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g).mapIso
      (adjunctionIso X f B hB g)).symm ≪≫
    ProjectivePureTrace.traceIso f.left B n (Fintype.card_fin (n + 2)) hB g
      s (section_eq X f s hs)

theorem traceIso_hom : (traceIso X f B hB g s hs).hom = trace X f B hB g := by
  change _ ≫ (ProjectivePureTrace.traceIso f.left B n
    (Fintype.card_fin (n + 2)) hB g s (section_eq X f s hs)).hom = _
  rw [ProjectivePureTrace.traceIso_hom]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveFormTrace
