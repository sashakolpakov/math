import OAI.AlgebraicGeometry.Comparison.Betti.MixedJetDifferential

/-! # Zero Jet Differential -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ZeroJetDifferential.Dolbeault

noncomputable section

/-! Decoding the zero-order mixed-jet differential on a parameter
direction gives the actual first parameter derivative array. -/

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem parameterJet_one_apply (g : P × ℂ → F) (q : P × ℂ) (v : P) :
    OperatorParameterJets.Dolbeault.parameterJet g 1 q (fun _ => v) = fderiv ℝ g q (v, 0) :=
  iteratedFDeriv_one_apply (fun _ => (v, (0 : ℂ)))

theorem zeroJet_differential_parameter_apply
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => P) F)
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => P) F) (v : P) :
    (continuousMultilinearCurryFin0 ℝ P F)
      ((MixedJetDifferential.Dolbeault.mixedJetParameterDifferential (P := P) (F := F) 0 A +
        MixedJetDifferential.Dolbeault.mixedJetLineDifferential (P := P) (F := F) 0 B) (v, 0)) = A (fun _ => v) := by
  change A (Fin.cons v (0 : Fin 0 → P)) + (0 : ℂ) • B (0 : Fin 0 → P) = A (fun _ => v)
  rw [zero_smul, add_zero]
  congr 1
  funext i
  fin_cases i
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.ZeroJetDifferential.Dolbeault
