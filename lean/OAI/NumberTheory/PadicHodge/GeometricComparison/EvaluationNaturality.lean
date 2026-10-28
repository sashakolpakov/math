import OAI.NumberTheory.PadicHodge.GeometricComparison.TensorDualExt

/-! # Evaluation Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.EvaluationNaturality.DualBaseChange

noncomputable section

/-! Naturality of a comparison follows from its evaluation formula and the two native evaluation pairings. -/

open scoped TensorProduct

variable {R S : Type*} [Field R] [Field S] [Algebra R S]
  {CX CY HX HY DX DY JX JY : Type*}
  [AddCommGroup CX] [Module R CX] [AddCommGroup CY] [Module R CY]
  [AddCommGroup HX] [Module R HX] [AddCommGroup HY] [Module R HY]
  [AddCommGroup DX] [Module S DX] [AddCommGroup DY] [Module S DY]
  [AddCommGroup JX] [Module S JX] [AddCommGroup JY] [Module S JY]

theorem evaluation_comparison_naturality
    (cX : (S ⊗[R] CX) ≃ₗ[S] DX) (cY : (S ⊗[R] CY) ≃ₗ[S] DY)
    (hX : (S ⊗[R] HX) ≃ₗ[S] JX) (hY : (S ⊗[R] HY) ≃ₗ[S] JY)
    (eRX : CX ≃ₗ[R] Module.Dual R HX) (eRY : CY ≃ₗ[R] Module.Dual R HY)
    (eSX : DX ≃ₗ[S] Module.Dual S JX) (eSY : DY ≃ₗ[S] Module.Dual S JY)
    (fR : CY →ₗ[R] CX) (fS : DY →ₗ[S] DX) (gR : HX →ₗ[R] HY) (gS : JX →ₗ[S] JY)
    (evalX : ∀ a c z, eSX (cX (a ⊗ₜ[R] c)) (hX (1 ⊗ₜ[R] z)) = a * algebraMap R S (eRX c z))
    (evalY : ∀ a c z, eSY (cY (a ⊗ₜ[R] c)) (hY (1 ⊗ₜ[R] z)) = a * algebraMap R S (eRY c z))
    (natR : ∀ c z, eRX (fR c) z = eRY c (gR z))
    (natS : ∀ c z, eSX (fS c) z = eSY c (gS z))
    (natH : ∀ z, hY (1 ⊗ₜ[R] gR z) = gS (hX (1 ⊗ₜ[R] z)))
    (a : S) (c : CY) : cX (a ⊗ₜ[R] fR c) = fS (cY (a ⊗ₜ[R] c)) := by
  apply eSX.injective
  apply TensorDualExt.DualBaseChange.ext_via_tensor hX
  intro z
  calc
    eSX (cX (a ⊗ₜ[R] fR c)) (hX (1 ⊗ₜ[R] z)) = a * algebraMap R S (eRX (fR c) z) :=
      evalX a (fR c) z
    _ = a * algebraMap R S (eRY c (gR z)) := congrArg (fun r => a * algebraMap R S r) (natR c z)
    _ = eSY (cY (a ⊗ₜ[R] c)) (hY (1 ⊗ₜ[R] gR z)) := (evalY a c (gR z)).symm
    _ = eSY (cY (a ⊗ₜ[R] c)) (gS (hX (1 ⊗ₜ[R] z))) := congrArg _ (natH z)
    _ = eSX (fS (cY (a ⊗ₜ[R] c))) (hX (1 ⊗ₜ[R] z)) :=
      (natS (cY (a ⊗ₜ[R] c)) (hX (1 ⊗ₜ[R] z))).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.EvaluationNaturality.DualBaseChange
