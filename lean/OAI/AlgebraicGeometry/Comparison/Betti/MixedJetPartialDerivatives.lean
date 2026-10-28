import OAI.AlgebraicGeometry.Comparison.Betti.ParameterJetDerivative
import OAI.AlgebraicGeometry.Comparison.Betti.MixedSliceParameterDerivative
import OAI.AlgebraicGeometry.Comparison.Betti.MixedJetAlgebra

/-! # Mixed Jet Partial Derivatives -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MixedJetPartialDerivatives.Dolbeault

noncomputable section

/-! The actual partial derivatives of every mixed parameter jet are the
two adjacent mixed jets, with their original multilinear normalization. -/

open Set
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F]

theorem hasFDerivAt_mixedParameterJet_parameter {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g)
    {U : Set ℂ} (hU : IsOpen U) (hhol : ∀ p : P, DifferentiableOn ℂ (fun z => g (p, z)) U)
    (k l : ℕ) (p : P) {z : ℂ} (hz : z ∈ U) :
    HasFDerivAt (fun x => MixedJetAlgebra.Dolbeault.mixedParameterJet g k l (x, z))
      (MixedJetAlgebra.Dolbeault.mixedParameterJet g (k + 1) l (p, z)).curryLeft p := by
  have h := MixedSliceParameterDerivative.Dolbeault.hasFDerivAt_iteratedHolomorphicSlice_parameter isOpen_univ hU
    (OperatorParameterJets.Dolbeault.parameterJet_contDiff hg k).contDiffOn
    (fun p _ => OperatorParameterJets.Dolbeault.parameterJet_holomorphic hg hU hhol k p) l (mem_univ p) hz
  have he : (fun w => Smooth.ContourDerivative.Dolbeault.circleParameterDerivative (OperatorParameterJets.Dolbeault.parameterJet g k) (p, w)) =
      (fun w => ParameterJetDerivative.Dolbeault.parameterJetCurryComplex (P := P) (F := F) k (OperatorParameterJets.Dolbeault.parameterJet g (k + 1) (p, w))) :=
    funext (fun w => ParameterJetDerivative.Dolbeault.circleParameterDerivative_parameterJet hg k (p, w))
  rw [he] at h
  have hmap := Holomorphic.DerivativeApproximation.Dolbeault.holomorphic_iteratedDeriv_map
    (F := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => P) F)
    (G := P →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F)
    (ParameterJetDerivative.Dolbeault.parameterJetCurryComplex (P := P) (F := F) k) hU
    (OperatorParameterJets.Dolbeault.parameterJet_holomorphic hg hU hhol (k + 1) p) l hz
  rw [hmap] at h
  exact h

theorem hasDerivAt_mixedParameterJet_line {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g)
    {U : Set ℂ} (hU : IsOpen U) (hhol : ∀ p : P, DifferentiableOn ℂ (fun z => g (p, z)) U)
    (k l : ℕ) (p : P) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w => MixedJetAlgebra.Dolbeault.mixedParameterJet g k l (p, w))
      (MixedJetAlgebra.Dolbeault.mixedParameterJet g k (l + 1) (p, z)) z := by
  have h := ((Holomorphic.DerivativeApproximation.Dolbeault.holomorphic_iteratedDeriv_on (OperatorParameterJets.Dolbeault.parameterJet_holomorphic hg hU hhol k p) hU l)
    z hz).differentiableAt (hU.mem_nhds hz)
  simpa only [MixedJetAlgebra.Dolbeault.mixedParameterJet, iteratedDeriv_succ] using h.hasDerivAt

end

end OAI.AlgebraicGeometry.Comparison.Betti.MixedJetPartialDerivatives.Dolbeault
