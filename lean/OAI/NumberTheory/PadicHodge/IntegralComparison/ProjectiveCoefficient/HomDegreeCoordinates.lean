import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterGlobalCoordinates

/-! # Hom Degree Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomDegreeCoordinates

noncomputable section

/-! Evaluation of the original coefficient adjunction after the same
explicit cohomological degree transport used by scalar adjunction. -/
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
  (g c : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  (hc : c = n-g) (j : Fin (n+1)) (B : ℕ) (hB : n+1≤B) (hg : g≤n)
def iso : (HomLocal.coefficientDual X f i j B).homology c ≅ HomLocal.targetSheaf X f i g :=
  eqToIso (congrArg (fun d => (HomLocal.coefficientDual X f i j B).homology d) hc) ≪≫
    HomGlobal.iso X f i g j B hB hg

variable (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (k : Fin (n+1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
local instance coefficient_qc : (HomLocal.coefficient X f i).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f i.left
local instance line_qc : (HomLocal.canonical (R := R) j).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (n+1))
theorem evaluation (z : Γ((HomLocal.coefficientDual X f i j B).homology c, U))
    (x : Γ(HomLocal.coefficient X f i, U)) :
    letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
    letI (q : ℕ) := HomLocal.scalar_dual_terms X i j B hB q
    letI (q : ℕ) := HomLocal.coefficient_dual_terms X f i j B hB q
    letI (q : ℕ) := HomLocal.scalar_projective X i j B U hU k hUk q
    letI (q : ℕ) := HomLocal.coefficient_term_projective X f i j B U hU k hUk q
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (HomLocal.coefficient X f i) (HomLocal.formSheaf X i g) U
      ((iso X f i g c hc j B hB hg).hom.app U z) x =
    (Projective.ParameterGlobalCoordinates.iso X i hc j B hB hg).hom.app U
      (Affine.CoefficientRestriction.pullback U hU (HomLocal.canonical j)
        (HomLocal.scalarComplex X i j B) (HomLocal.coefficientComplex X f i j B) (HomLocal.scalar X i) (HomLocal.coefficient X f i)
        (Projective.NegativeResolution.augmentation (HomLocal.scalar X i) j B)
        (Projective.NegativeResolution.augmentation (HomLocal.coefficient X f i) j B)
        (Finite.FlatCoefficientSections.quotientRing i.left U) (Finite.FlatCoefficientSections.coefficientRing f i.left U)
        (FiniteCoefficient.RestrictionNormalization.scalarChartIso i.left U hU)
        (Finite.FlatCoefficientSections.chartIso f i.left U hU) c z
        (Affine.IntrinsicCoefficientHom.coefficientIso U hU (HomLocal.coefficient X f i)
          (Finite.FlatCoefficientSections.coefficientRing f i.left U) (Finite.FlatCoefficientSections.chartIso f i.left U hU) x)) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let (q : ℕ) := HomLocal.scalar_dual_terms X i j B hB q
  let (q : ℕ) := HomLocal.coefficient_dual_terms X f i j B hB q
  let (q : ℕ) := HomLocal.scalar_projective X i j B U hU k hUk q
  let (q : ℕ) := HomLocal.coefficient_term_projective X f i j B U hU k hUk q
  subst c
  exact HomEvaluation.evaluation X f i g j B hB hg U hU k hUk z x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomDegreeCoordinates
