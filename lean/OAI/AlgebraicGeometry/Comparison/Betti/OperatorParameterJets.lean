import OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialParameterJets
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ParameterJets
import OAI.AlgebraicGeometry.Comparison.Betti.SeparatedHolomorphicFamilies

/-! # Operator Parameter Jets -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.OperatorParameterJets.Dolbeault

noncomputable section

/-! The actual parameter derivative arrays as Banach-valued functions.
They are holomorphic in the complex-line variable, and the original
Cauchy partial sum commutes with the entire array. -/

open Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def parameterJet (g : P × ℂ → F) (k : ℕ) (q : P × ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F :=
  (iteratedFDeriv ℝ k g q).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ P ℂ)

def realMultilinearComplexEvaluation {k : ℕ} (v : Fin k → P) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F →L[ℂ] F where
  toFun T := T v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P) F v).continuous

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem parameterJet_contDiff {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    ContDiff ℝ ∞ (parameterJet g k) :=
  (ContinuousMultilinearMap.compContinuousLinearMapL (F := F)
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ P ℂ)).contDiff.comp
      (hg.iteratedFDeriv_right (m := ∞)
        (WithTop.coe_le_coe.mpr (le_top : (⊤ : ℕ∞) + (k : ℕ∞) ≤ ⊤)))

theorem parameterJet_cauchyPolynomial [FiniteDimensional ℝ P] [CompleteSpace F]
    {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (N k : ℕ) (q : P × ℂ) :
    parameterJet (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) k q =
      Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (parameterJet g k) c r N q := by
  have hc : ContinuousOn (fun z => parameterJet g k (q.1, z)) (sphere c r) :=
    ((parameterJet_contDiff hg k).continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
  apply ContinuousMultilinearMap.ext
  intro v
  have hfirst := CauchyPolynomialParameterJets.Dolbeault.cauchyParameterPolynomial_parameter_jet hg c hr N k v q
  have hsecond := CauchyPolynomialNaturality.Dolbeault.cauchyPowerSeries_partialSum_map
    (F := ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F) (G := F)
    (realMultilinearComplexEvaluation (F := F) v) hr hc N q.2
  exact hfirst.trans hsecond.symm

theorem parameterJet_holomorphic [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [CompleteSpace F]
    {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g) {U : Set ℂ} (hU : IsOpen U)
    (hhol : ∀ p : P, DifferentiableOn ℂ (fun z => g (p, z)) U) (k : ℕ) (p : P) :
    DifferentiableOn ℂ (fun z => parameterJet g k (p, z)) U := by
  apply SeparatedHolomorphicFamilies.Dolbeault.separatingFamily_holomorphic (fun v : Fin k → P => realMultilinearComplexEvaluation v)
    (fun x y he => ContinuousMultilinearMap.ext he) hU
    (((parameterJet_contDiff hg k).continuous.comp (continuous_const.prodMk continuous_id)).continuousOn)
  intro v
  exact Holomorphic.ParameterJets.Dolbeault.holomorphicSlice_iteratedDerivative isOpen_univ hU hg.contDiffOn
    (fun q _ => hhol q) k (fun i => (v i, 0)) p (mem_univ _)

end

end OAI.AlgebraicGeometry.Comparison.Betti.OperatorParameterJets.Dolbeault
