import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomDegreeCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.VectorCoordinates

/-! # Coefficient Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientEvaluation

noncomputable section

/-! The original coefficient adjunction evaluates a literal finite
section in the same affine coordinates, before geometric residue data
are supplied. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Finite.FlatCoefficientSections.quotientAlgebra
  Finite.FlatCoefficientSections.coefficientAlgebra
  Finite.FlatCoefficientSections.ambientAlgebra
  ProjectiveCoefficient.HomLocal.scalar_terms
  ProjectiveCoefficient.HomLocal.coefficient_terms
variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R n) [IsClosedImmersion i.left]
  (g c : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  (hc : c = n-g) (j : Fin (n+1)) (B : ℕ) (hB : n+1≤B) (hg : g≤n)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (k : Fin (n+1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
local instance coefficient_qc : (ProjectiveCoefficient.HomLocal.coefficient X f i).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f i.left
local instance line_qc : (ProjectiveCoefficient.HomLocal.canonical (R := R) j).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (n+1))

theorem evaluation (z : Γ((ProjectiveCoefficient.HomLocal.coefficientDual X f i j B).homology c, U))
    (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
    letI (q : ℕ) := ProjectiveCoefficient.HomLocal.scalar_dual_terms X i j B hB q
    letI (q : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_dual_terms X f i j B hB q
    letI (q : ℕ) := ProjectiveCoefficient.HomLocal.scalar_projective X i j B U hU k hUk q
    letI (q : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_term_projective X f i j B U hU k hUk q
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (ProjectiveCoefficient.HomLocal.coefficient X f i) (ProjectiveCoefficient.HomLocal.formSheaf X i g) U
      ((ProjectiveCoefficient.HomDegreeCoordinates.iso X f i g c hc j B hB hg).hom.app U z) x =
    (Projective.ParameterGlobalCoordinates.iso X i hc j B hB hg).hom.app U
      (Affine.CoefficientRestriction.pullback U hU (ProjectiveCoefficient.HomLocal.canonical j)
        (ProjectiveCoefficient.HomLocal.scalarComplex X i j B) (ProjectiveCoefficient.HomLocal.coefficientComplex X f i j B) (ProjectiveCoefficient.HomLocal.scalar X i) (ProjectiveCoefficient.HomLocal.coefficient X f i)
        (Projective.NegativeResolution.augmentation (ProjectiveCoefficient.HomLocal.scalar X i) j B)
        (Projective.NegativeResolution.augmentation (ProjectiveCoefficient.HomLocal.coefficient X f i) j B)
        (Finite.FlatCoefficientSections.quotientRing i.left U) (Finite.FlatCoefficientSections.coefficientRing f i.left U)
        (FiniteCoefficient.RestrictionNormalization.scalarChartIso i.left U hU)
        (Finite.FlatCoefficientSections.chartIso f i.left U hU) c z x) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let (q : ℕ) := ProjectiveCoefficient.HomLocal.scalar_dual_terms X i j B hB q
  let (q : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_dual_terms X f i j B hB q
  let (q : ℕ) := ProjectiveCoefficient.HomLocal.scalar_projective X i j B U hU k hUk q
  let (q : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_term_projective X f i j B U hU k hUk q
  exact (ProjectiveCoefficient.HomDegreeCoordinates.evaluation
    X f i g c hc j B hB hg U hU k hUk z x).trans
    (congrArg (fun v => (Projective.ParameterGlobalCoordinates.iso X i hc j B hB hg).hom.app U
      (Affine.CoefficientRestriction.pullback U hU (ProjectiveCoefficient.HomLocal.canonical j)
        (ProjectiveCoefficient.HomLocal.scalarComplex X i j B) (ProjectiveCoefficient.HomLocal.coefficientComplex X f i j B) (ProjectiveCoefficient.HomLocal.scalar X i) (ProjectiveCoefficient.HomLocal.coefficient X f i)
        (Projective.NegativeResolution.augmentation (ProjectiveCoefficient.HomLocal.scalar X i) j B)
        (Projective.NegativeResolution.augmentation (ProjectiveCoefficient.HomLocal.coefficient X f i) j B)
        (Finite.FlatCoefficientSections.quotientRing i.left U) (Finite.FlatCoefficientSections.coefficientRing f i.left U)
        (FiniteCoefficient.RestrictionNormalization.scalarChartIso i.left U hU)
        (Finite.FlatCoefficientSections.chartIso f i.left U hU) c z v))
      (FiniteCoefficient.VectorCoordinates.coefficient f i.left U hU x))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientEvaluation
