import OAI.AlgebraicGeometry.Comparison.Betti.OperatorParameterJets
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.HolomorphicSliceDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Mixed Jet Algebra -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MixedJetAlgebra.Dolbeault

noncomputable section

/-! Actual mixed derivative arrays, their joint smoothness, and their
linearity under subtraction of smooth holomorphic families. -/

open Set
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def mixedParameterJet (g : P × ℂ → F) (k l : ℕ) (q : P × ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F :=
  iteratedDeriv l (fun z => OperatorParameterJets.Dolbeault.parameterJet g k (q.1, z)) q.2

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem parameterJet_sub {g h : P × ℂ → F} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (k : ℕ) (q : P × ℂ) :
    OperatorParameterJets.Dolbeault.parameterJet (fun y => g y - h y) k q = OperatorParameterJets.Dolbeault.parameterJet g k q - OperatorParameterJets.Dolbeault.parameterJet h k q := by
  have hn : (k : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hd : iteratedFDeriv ℝ k (fun y => g y - h y) q =
      iteratedFDeriv ℝ k g q - iteratedFDeriv ℝ k h q :=
    iteratedFDeriv_sub_apply (hg.of_le hn).contDiffAt (hh.of_le hn).contDiffAt
  unfold OperatorParameterJets.Dolbeault.parameterJet
  rw [hd]
  apply ContinuousMultilinearMap.ext
  intro v
  rfl

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem norm_parameterJet_zero (g : P × ℂ → F) (q : P × ℂ) : ‖OperatorParameterJets.Dolbeault.parameterJet g 0 q‖ = ‖g q‖ := by
  have he : OperatorParameterJets.Dolbeault.parameterJet g 0 q = (continuousMultilinearCurryFin0 ℝ P F).symm (g q) := by
    apply ContinuousMultilinearMap.ext
    intro v
    rfl
  rw [he, LinearIsometryEquiv.norm_map]

theorem norm_mixedParameterJet_zero (g : P × ℂ → F) (q : P × ℂ) :
    ‖mixedParameterJet g 0 0 q‖ = ‖g q‖ :=
  norm_parameterJet_zero g q

variable [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [CompleteSpace F]

theorem mixedParameterJet_smooth {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g) {U : Set ℂ} (hU : IsOpen U)
    (hhol : ∀ p : P, DifferentiableOn ℂ (fun z => g (p, z)) U) (k l : ℕ) :
    ContDiffOn ℝ ∞ (mixedParameterJet g k l) (univ ×ˢ U) :=
  Smooth.HolomorphicSliceDerivatives.Dolbeault.holomorphicSlice_iteratedDeriv_smooth isOpen_univ hU (OperatorParameterJets.Dolbeault.parameterJet_contDiff hg k).contDiffOn
    (fun p _ => OperatorParameterJets.Dolbeault.parameterJet_holomorphic hg hU hhol k p) l

theorem mixedParameterJet_sub {g h : P × ℂ → F} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    {U : Set ℂ} (hU : IsOpen U)
    (hgol : ∀ p : P, DifferentiableOn ℂ (fun z => g (p, z)) U)
    (hhol : ∀ p : P, DifferentiableOn ℂ (fun z => h (p, z)) U)
    (k l : ℕ) {q : P × ℂ} (hq : q.2 ∈ U) :
    mixedParameterJet (fun y => g y - h y) k l q = mixedParameterJet g k l q - mixedParameterJet h k l q := by
  have he : (fun z => OperatorParameterJets.Dolbeault.parameterJet (fun y => g y - h y) k (q.1, z)) =
      (fun z => OperatorParameterJets.Dolbeault.parameterJet g k (q.1, z) - OperatorParameterJets.Dolbeault.parameterJet h k (q.1, z)) :=
    funext (fun z => parameterJet_sub hg hh k (q.1, z))
  unfold mixedParameterJet
  rw [he]
  exact iteratedDeriv_fun_sub
    (((OperatorParameterJets.Dolbeault.parameterJet_holomorphic hg hU hgol k q.1).contDiffOn hU).contDiffAt (hU.mem_nhds hq))
    (((OperatorParameterJets.Dolbeault.parameterJet_holomorphic hh hU hhol k q.1).contDiffOn hU).contDiffAt (hU.mem_nhds hq))

end

end OAI.AlgebraicGeometry.Comparison.Betti.MixedJetAlgebra.Dolbeault
