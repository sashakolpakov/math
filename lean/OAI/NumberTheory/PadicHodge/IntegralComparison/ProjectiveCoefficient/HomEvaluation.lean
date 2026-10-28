import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomGlobal

/-! # Hom Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomEvaluation

noncomputable section

/-! The actual global coefficient adjunction is normalized by every
local coefficient section, not only by the coefficient unit. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal
open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
attribute [local instance] HomLocal.scalar_terms
attribute [local instance] HomLocal.coefficient_terms
variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R n) [IsClosedImmersion i.left]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  (j : Fin (n+1)) (B : ℕ) (hB : n+1 ≤ B) (hg : g ≤ n)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (k : Fin (n+1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)

abbrev evaluation (z : Γ(HomLocal.sourceSheaf X f i g j B, U)) (x : Γ(HomLocal.coefficient X f i, U)) := by
  letI : (HomLocal.coefficient X f i).IsQuasicoherent := Finite.MapPureTrace.coefficients_quasicoherent f i.left
  letI : (HomLocal.canonical (R := R) j).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (n+1))
  letI := HomLocal.formScalar X i g U
  letI := HomLocal.formTower X i g U
  letI (q : ℕ) := HomLocal.scalar_dual_terms X i j B hB q
  letI (q : ℕ) := HomLocal.coefficient_dual_terms X f i j B hB q
  letI := HomLocal.coefficient_finite X f i U hU
  letI := HomLocal.coefficient_projective X f i U hU
  letI (q : ℕ) := HomLocal.scalar_projective X i j B U hU k hUk q
  letI (q : ℕ) := HomLocal.coefficient_term_projective X f i j B U hU k hUk q
  have hl := Affine.IntrinsicCoefficientHom.evaluation U hU (HomLocal.canonical j)
    (HomLocal.scalarComplex X i j B) (HomLocal.coefficientComplex X f i j B) (HomLocal.scalar X i) (HomLocal.coefficient X f i)
    (Projective.NegativeResolution.augmentation (HomLocal.scalar X i) j B)
    (Projective.NegativeResolution.augmentation (HomLocal.coefficient X f i) j B)
    (Finite.FlatCoefficientSections.quotientRing i.left U) (i.left.app_surjective U hU) (Finite.FlatCoefficientSections.coefficientRing f i.left U)
    (FiniteCoefficient.RestrictionNormalization.scalarChartIso i.left U hU)
    (Finite.FlatCoefficientSections.chartIso f i.left U hU) (n-g) (HomLocal.formSheaf X i g)
    (HomLocal.scalarAdjunction X i g j B hB hg) z x
  have hglobal := HomGlobal.iso_app X f i g j B hB hg U hU ⟨k,hUk⟩ z
  have hsection : (HomGlobal.chosenSectionIso X f i g j B hB hg
      U hU ⟨k,hUk⟩).hom z = (HomLocal.sectionIso X f i g j B hB hg U hU k hUk).hom z := rfl
  exact (congrArg (fun y => ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (HomLocal.coefficient X f i)
    (HomLocal.formSheaf X i g) U y x) (hglobal.trans hsection)).trans hl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomEvaluation
