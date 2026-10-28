import OAI.AlgebraicGeometry.Comparison.Betti.OperatorParameterJets

/-! # Parameter Jet Derivative -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ParameterJetDerivative.Dolbeault

noncomputable section

/-! The actual parameter derivative of a multilinear parameter jet is
the next jet, with its first argument curried as a continuous linear map. -/

open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_parameterJet {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g)
    (k : ℕ) (p : P) (z : ℂ) :
    HasFDerivAt (fun x => OperatorParameterJets.Dolbeault.parameterJet g k (x, z))
      (OperatorParameterJets.Dolbeault.parameterJet g (k + 1) (p, z)).curryLeft p := by
  let R := ContinuousMultilinearMap.compContinuousLinearMapL (F := F)
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ P ℂ)
  have hd := (hg.contDiffAt (x := (p, z))).differentiableAt_iteratedFDeriv
    (m := k) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  have hactual := (R.hasFDerivAt.comp (p, z) hd.hasFDerivAt).comp p
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) p z)
  convert hactual using 1 <;> rfl

theorem circleParameterDerivative_parameterJet {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g)
    (k : ℕ) (q : P × ℂ) :
    Smooth.ContourDerivative.Dolbeault.circleParameterDerivative (OperatorParameterJets.Dolbeault.parameterJet g k) q = (OperatorParameterJets.Dolbeault.parameterJet g (k + 1) q).curryLeft := by
  have hd : DifferentiableAt ℝ (OperatorParameterJets.Dolbeault.parameterJet g k) q :=
    (OperatorParameterJets.Dolbeault.parameterJet_contDiff hg k).differentiable (by simp) q
  have hactual : HasFDerivAt (fun p => OperatorParameterJets.Dolbeault.parameterJet g k (p, q.2))
      (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative (OperatorParameterJets.Dolbeault.parameterJet g k) q) q.1 := by
    change HasFDerivAt (OperatorParameterJets.Dolbeault.parameterJet g k ∘ fun p => (p, q.2))
      ((fderiv ℝ (OperatorParameterJets.Dolbeault.parameterJet g k) q).comp (ContinuousLinearMap.inl ℝ P ℂ)) q.1
    exact hd.hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)
  exact hactual.unique (hasFDerivAt_parameterJet hg k q.1 q.2)

variable [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def parameterJetCurryComplex (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => P) F →L[ℂ]
      (P →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F) where
  toFun T := T.curryLeft
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F).continuous

end

end OAI.AlgebraicGeometry.Comparison.Betti.ParameterJetDerivative.Dolbeault
