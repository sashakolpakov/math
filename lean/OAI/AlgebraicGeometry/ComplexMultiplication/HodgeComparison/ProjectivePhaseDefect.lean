import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveConnectionCech

/-! # Projective Phase Defect -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectivePhaseDefect.CM.Construction

noncomputable section

/-! The Čech coboundary of the actual smooth phase cochain is
precisely the rational logarithmic defect, viewed as locally constant forms. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

theorem normalizedImaginaryPart_integer_period (n : ℤ) :
    LogarithmicPhase.CM.Construction.normalizedImaginaryPart ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = (n : ℂ) := by
  rw [LogarithmicPhase.CM.Construction.normalizedImaginaryPart_apply]
  simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, zero_mul, mul_zero, zero_add, add_zero, mul_one, sub_zero]
  rw [mul_div_cancel_right₀ _ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero),
    Complex.ofReal_intCast]

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def rationalLocallyConstantManifoldForm (U : Opens M) (f : LocallyConstant U ℚ) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantManifoldZeroForm E U
    ⟨fun x => (f x : ℂ), f.isLocallyConstant.comp (fun q : ℚ => (q : ℂ))⟩

theorem rationalLocallyConstantManifoldForm_apply (U : Opens M) (f : LocallyConstant U ℚ)
    (x : U) (v : Fin 0 → TangentSpace 𝓘(ℝ, E) x.val) :
    rationalLocallyConstantManifoldForm (E := E) U f x v = (f x : ℂ) :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantManifoldZeroForm_apply U _ x v

def rationalCechManifoldForm {I : Type} (U : I → Opens M) (n : ℕ)
    (c : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain
      (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf (TopCat.of M)) U n) :
    Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U 0 n :=
  fun a => rationalLocallyConstantManifoldForm _ (c a)

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] [NormalSpace M]
  {ι : Type} [Fintype ι]
  (p : M → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)
  (hhol : ∀ i, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞
    (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i) (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i : Set M))

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem projectivePhaseCech_apply (a : Fin 2 → M × ι)
    (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) a)
    (v : Fin 0 → TangentSpace 𝓘(ℝ, E) x.val) :
    ProjectiveConnectionCech.CM.Construction.projectivePhaseCech p hp hhol a x v = LogarithmicPhase.CM.Construction.normalizedImaginaryPart (ProjectiveChernCocycle.CM.Construction.projectiveLogCech p hp hhol a x) := rfl

theorem projectivePhaseCech_delta :
    Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 0 1 (ProjectiveConnectionCech.CM.Construction.projectivePhaseCech p hp hhol) =
      rationalCechManifoldForm (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 2
        (DivisorClass.Chern.LogCech.RationalCech.logDefectCech (TopCat.of M) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)
          (ProjectiveChernCocycle.CM.Construction.projectiveLogCech p hp hhol) (ProjectiveChernCocycle.CM.Construction.projectiveLogCech_cocycle p hp hhol)) := by
  funext a
  have hdelta := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta_apply (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E M 0) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)
    1 (ProjectiveConnectionCech.CM.Construction.projectivePhaseCech p hp hhol) a
  refine hdelta.trans ?_
  rw [Fin.sum_univ_three]
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  let U := ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol
  let l := ProjectiveChernCocycle.CM.Construction.projectiveLogCech p hp hhol
  let edge := fun j : Fin 3 => DivisorClass.Chern.LogCech.RationalCech.edgeLog (TopCat.of M) U l j a x
  let hc := ProjectiveChernCocycle.CM.Construction.projectiveLogCech_cocycle p hp hhol a x
  have hs := DivisorClass.Chern.Logarithms.Construction.logarithmicDefect_spec (edge 2) (edge 0) (edge 1) hc
  have hn := congrArg LogarithmicPhase.CM.Construction.normalizedImaginaryPart hs
  rw [map_sub, map_add, normalizedImaginaryPart_integer_period] at hn
  change (1 : ℤ) • LogarithmicPhase.CM.Construction.normalizedImaginaryPart (edge 0) +
    (-1 : ℤ) • LogarithmicPhase.CM.Construction.normalizedImaginaryPart (edge 1) +
    (1 : ℤ) • LogarithmicPhase.CM.Construction.normalizedImaginaryPart (edge 2) = _
  change (1 : ℤ) • LogarithmicPhase.CM.Construction.normalizedImaginaryPart (edge 0) +
    (-1 : ℤ) • LogarithmicPhase.CM.Construction.normalizedImaginaryPart (edge 1) +
    (1 : ℤ) • LogarithmicPhase.CM.Construction.normalizedImaginaryPart (edge 2) =
      rationalLocallyConstantManifoldForm (E := E) _
        (DivisorClass.Chern.LogCech.RationalCech.logDefectCech (TopCat.of M) U l
          (ProjectiveChernCocycle.CM.Construction.projectiveLogCech_cocycle p hp hhol) a) x v
  rw [rationalLocallyConstantManifoldForm_apply]
  change _ = (((DivisorClass.Chern.Logarithms.Construction.logarithmicDefect (edge 2) (edge 0) (edge 1) hc : ℤ) : ℚ) : ℂ)
  push_cast
  simp only [one_smul, neg_one_smul]
  calc
    _ = LogarithmicPhase.CM.Construction.normalizedImaginaryPart (edge 2) + LogarithmicPhase.CM.Construction.normalizedImaginaryPart (edge 0) -
        LogarithmicPhase.CM.Construction.normalizedImaginaryPart (edge 1) := by ring
    _ = _ := hn

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectivePhaseDefect.CM.Construction
