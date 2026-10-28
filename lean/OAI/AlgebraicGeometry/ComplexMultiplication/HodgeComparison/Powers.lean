import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ConstantFormUnit
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCupUnit
import OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointConjugation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PureOneCovector

/-! # Powers -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Powers.CM.Construction

noncomputable section

section

/-! Actual closed powers of the projective Kähler form, their pure
bidegrees, and their canonical rational cup-product classes. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions
open scoped _root_.Manifold ContDiff

def fubiniStudyPower (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (k : ℕ) → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (k + k)
  | 0 => ConstantFormUnit.CM.Construction.constantClosedZeroForm V.analyticModel V.analyticSpace 1
  | k + 1 => AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldDegreeCast (by omega)
      (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (fubiniStudyPower V k) (ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm V))

def fubiniStudyPowerQ (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : (k : ℕ) → V.rationalCohomology (k + k)
  | 0 => AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit (R := ℚ) (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace V.toOver))
  | k + 1 => cast (congrArg (fun n => (V.rationalCohomology n : Type)) (by omega : (k + k) + 2 = (k + 1) + (k + 1)))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) (k + k) 2
        (fubiniStudyPowerQ V k) (ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V))

theorem fubiniStudyPower_hasBidegree (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace k k (Construction.fubiniStudyPower V k).val.val := by
  induction k with
  | zero => intro e he y hy; exact Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero (E := V.analyticModel) _
  | succ k hk =>
      exact AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.hasManifoldBidegree_wedge hk (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm_hasBidegree V)

theorem fubiniStudyPower_comparison (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    (V.deRhamBettiIso (k + k)).hom (V.deRhamClass (k + k) (Construction.fubiniStudyPower V k)) =
      V.rationalCohomologyInclusion (k + k) (Construction.fubiniStudyPowerQ V k) := by
  induction k with
  | zero =>
      exact (ConstantFormUnit.CM.Construction.constantOneForm_bettiClass V).trans
        (RationalCupUnit.CM.Construction.rationalToComplexCohomology_unit (Betti.Scheme.schemePointSpace V.toOver)).symm
  | succ k hk =>
      have hform := AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass_cast V
        (by omega : (k + k) + 2 = (k + 1) + (k + 1))
        (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (Construction.fubiniStudyPower V k) (ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm V))
      have hw := AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass_wedge V (Construction.fubiniStudyPower V k) (ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm V)
      have hq := RationalCupUnit.CM.Construction.rationalToComplexCohomology_cast (Betti.Scheme.schemePointSpace V.toOver)
        (by omega : (k + k) + 2 = (k + 1) + (k + 1))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) (k + k) 2
          (Construction.fubiniStudyPowerQ V k) (ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V))
      have hcup := RationalCup.CM.Construction.rationalToComplexCohomology_cup (Betti.Scheme.schemePointSpace V.toOver) (k + k) 2
        (Construction.fubiniStudyPowerQ V k) (ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V)
      have hbase : AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V 2 (ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm V) =
          V.rationalCohomologyInclusion 2 (ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V) := ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ_comparison V
      change AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V (k + k) (Construction.fubiniStudyPower V k) = _ at hk
      rw [hbase, hk] at hw
      let transport := cast (congrArg (fun n => (V.complexCohomology n : Type))
        (by omega : (k + k) + 2 = (k + 1) + (k + 1)))
      exact hform.trans ((congrArg transport (hw.trans hcup.symm)).trans hq.symm)

end

section

/-! Exterior multiplication and the actual Kähler powers commute with
pointwise complex conjugation. -/

open OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions
open scoped _root_.Manifold ContDiff

theorem covectorWedge_conjugate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E p) (b : Analysis.DifferentialForms.Manifold.Basic.FormValue E q) :
    Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b) =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap a)
        (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap b) := by
  ext v
  change star (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b v) = _
  rw [AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_apply, AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_apply]
  change star ((((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) •
    ∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
      (a (fun i => v (σ (Fin.castAdd q i))) * b (fun i => v (σ (Fin.natAdd p i))))) =
    (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) •
      ∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
        (star (a (fun i => v (σ (Fin.castAdd q i)))) * star (b (fun i => v (σ (Fin.natAdd p i)))))
  simp only [Units.smul_def, star_smul, star_trivial, star_sum, star_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact congrArg (fun z : ℂ => (Equiv.Perm.sign σ : ℤ) • z) (mul_comm _ _)

theorem conjugateClosedForm_wedge
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {p q : ℕ} (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    Conjugation.CM.Construction.conjugateClosedForm (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge a b) =
      AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (Conjugation.CM.Construction.conjugateClosedForm a) (Conjugation.CM.Construction.conjugateClosedForm b) := by
  apply Subtype.ext
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (NormedSpace ℝ E)
  exact covectorWedge_conjugate (a.val x) (b.val x)

theorem conjugateClosedForm_degreeCast
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {n m : ℕ} (h : n = m) (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    Conjugation.CM.Construction.conjugateClosedForm (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldDegreeCast h a) =
      AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldDegreeCast h (Conjugation.CM.Construction.conjugateClosedForm a) := by
  subst m
  rfl

theorem fubiniStudyClosedForm_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Conjugation.CM.Construction.conjugateClosedForm (ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm V) = ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm V := by
  apply Subtype.ext
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  change star (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x v) = IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x v
  apply Complex.ext
  · rfl
  · simp only [Complex.star_def, Complex.conj_im, VarietyMetric.CM.Construction.varietyFubiniStudyForm_real, neg_zero]

theorem fubiniStudyPower_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    Conjugation.CM.Construction.conjugateClosedForm (Construction.fubiniStudyPower V k) = Construction.fubiniStudyPower V k := by
  induction k with
  | zero =>
      apply Subtype.ext
      apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
      intro x
      ext v
      have hv : v = 0 := by ext i; exact Fin.elim0 i
      rw [hv]
      change star (HolomorphicPrimitive.CM.Construction.zeroFormScalar (NormalizedPrimitives.CM.Construction.constantZeroForm V.analyticModel V.analyticSpace 1) x) =
        HolomorphicPrimitive.CM.Construction.zeroFormScalar (NormalizedPrimitives.CM.Construction.constantZeroForm V.analyticModel V.analyticSpace 1) x
      rw [NormalizedPrimitives.CM.Construction.constantZeroForm_scalar, star_one]
  | succ k hk =>
      change Conjugation.CM.Construction.conjugateClosedForm (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldDegreeCast _
        (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (Construction.fubiniStudyPower V k) (ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm V))) = _
      rw [conjugateClosedForm_degreeCast, conjugateClosedForm_wedge, hk, fubiniStudyClosedForm_conjugate]
      rfl

end

/-! The actual real two-form i α ∧ conjugate(α) is positive on each
complex line where the holomorphic covector α is nonzero. -/

open OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covectorWedge_one_one (a b : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (v : Fin 2 → E) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b v = a (fun _ => v 0) * b (fun _ => v 1) -
      a (fun _ => v 1) * b (fun _ => v 0) := by
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_apply]
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, inv_one, one_smul, hperm]
  rw [Finset.sum_pair (by decide : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1)]
  simp [Fin.fin_one_eq_zero, sub_eq_add_neg]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def holomorphicRankOneForm (a : E →L[ℂ] ℂ) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2 :=
  Complex.I • AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E a)
    (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E a))

theorem holomorphicRankOneForm_complex_line (a : E →L[ℂ] ℂ) (u : E) :
    holomorphicRankOneForm a ![u, Complex.I • u] = (2 * Complex.normSq (a u) : ℝ) := by
  change Complex.I * AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E a)
    (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E a))
      ![u, Complex.I • u] = _
  rw [covectorWedge_one_one]
  change Complex.I * (a u * star (a (Complex.I • u)) - a (Complex.I • u) * star (a u)) = _
  rw [map_smul]
  simp only [smul_eq_mul, star_mul, Complex.star_def, Complex.conj_I]
  calc
    _ = 2 * (a u * star (a u)) := by
      change _ = 2 * (a u * (starRingEnd ℂ) (a u))
      ring_nf
      simp only [Complex.I_sq]
      ring
    _ = _ := by
      rw [Complex.star_def, Complex.mul_conj]
      push_cast
      rfl

theorem holomorphicRankOneForm_positive (a : E →L[ℂ] ℂ) (u : E) (hu : a u ≠ 0) :
    0 < (holomorphicRankOneForm a ![u, Complex.I • u]).re := by
  rw [holomorphicRankOneForm_complex_line, Complex.ofReal_re]
  exact mul_pos (by norm_num) (Complex.normSq_pos.mpr hu)

theorem holomorphicRankOneForm_nonnegative (a : E →L[ℂ] ℂ) (u : E) :
    0 ≤ (holomorphicRankOneForm a ![u, Complex.I • u]).re := by
  rw [holomorphicRankOneForm_complex_line, Complex.ofReal_re]
  exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Powers.CM.Construction
