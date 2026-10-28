import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.UnitNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.PointEvaluation

/-! # Unit Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.UnitEvaluation

noncomputable section

/-! The original common-refinement dual of the function pullback unit
is literal evaluation at one under the intrinsic coefficient adjunction. -/

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
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)

local instance : (HomLocal.coefficient X f i).IsQuasicoherent := Finite.MapPureTrace.coefficients_quasicoherent f i.left
local instance : (HomLocal.coefficient X f i).IsFiniteType := Finite.MapPureTrace.coefficients_finiteType f i.left

def dualUnit : HomLocal.sourceSheaf X f i g j B ⟶ (HomLocal.scalarDual X i j B).homology (n - g) :=
  ProjectiveRefinement.DualMap.map (HomLocal.scalar X i) (HomLocal.coefficient X f i) j B (n + 1) hB
    (Cech.StructurePullbackUnit.sheafMap f i.left) (n - g)

variable (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (k : Fin (n + 1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)

abbrev evaluation (z : Γ(HomLocal.sourceSheaf X f i g j B, U)) := by
  letI := HomLocal.formScalar X i g U
  letI := HomLocal.formTower X i g U
  letI := HomLocal.coefficient_finite X f i U hU
  letI := HomLocal.coefficient_projective X f i U hU
  exact ProjectiveRefinement.PointEvaluation.evaluation (HomLocal.scalar X i) (HomLocal.coefficient X f i)
    j B (n + 1) hB (Cech.StructurePullbackUnit.sheafMap f i.left) U hU k hUk
    (Finite.FlatCoefficientSections.quotientRing i.left U) (Finite.FlatCoefficientSections.coefficientRing f i.left U)
    (FiniteCoefficient.RestrictionNormalization.scalarChartIso i.left U hU)
    (Finite.FlatCoefficientSections.chartIso f i.left U hU) 1
    (FiniteCoefficient.UnitNormalization.chart_square f i.left U hU)
    (i.left.app_surjective U hU) (n - g) (HomLocal.formSheaf X i g)
    (HomLocal.scalarAdjunction X i g j B hB hg)
    (show Γ(HomLocal.coefficient X f i, U) from (1 : Γ(Y, f ⁻¹ᵁ (i.left ⁻¹ᵁ U))))
    (FiniteCoefficient.UnitNormalization.coefficient_one f i.left U hU) z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.UnitEvaluation
