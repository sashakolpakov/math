import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Tensor
import OAI.Analysis.PDE.Elliptic.Boundary.Third.Jet

open Set
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.Normed.Function.Holder

@[instance_reducible]
private def fourthJetHolderNorm (X Y : Type*) [MetricSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (α : ℝ) : Norm (OAI.Analysis.Normed.Function.Holder.HolderMap X Y α) :=
  inferInstance

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I
local instance fourthJetFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthJetFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthJetSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthJetSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthJetThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthJetThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthJetFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthJetFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthJetNorm {S : Set E} {α : ℝ} :
    Norm (OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α) :=
  fourthJetHolderNorm _ _ α

/-- First recover the third derivative of the normal first derivative. -/
theorem exists_uniform_normal_third_holder
    {α μ N : ℝ} (hα : 0 ≤ α) (hμ : 0 < μ) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (S : Set E) (u : E → ℝ), ContDiff ℝ 4 u → ∀ k : I,
      ∀ (a : E → Matrix I I ℝ) (A : I × I → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
        (R : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α) (T : I → OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α),
      (∀ p (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p) x = a x p.1 p.2) →
      (∀ p, ‖A p‖ ≤ N) →
      (∀ i, i ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T i) x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)))) x) →
      ∀ M Q, 0 ≤ M → 0 ≤ Q → (∀ i, i ≠ k → ‖T i‖ ≤ M) → ‖R‖ ≤ Q →
      (∀ x : S, μ ≤ a x k k) →
      (∀ x : S, OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))
          (EuclideanSpace.single k 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) →
      ∃ W : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
        (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value W x =
          fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1)))) x) ∧
            ‖W‖ ≤ C*(M+Q) := by
  classical
  obtain ⟨C,hC,hrecover⟩ := exists_uniform_third_holder (I := I) hα hμ hN
  refine ⟨C,hC,?_⟩
  intro S u hu k a A R T hA hAn hT M Q hM hQ hTn hRn hpos heq
  let B (i : I) := holderEvaluate (T i) (EuclideanSpace.single k 1)
  have hB (i : I) (hi : i ≠ k) (x : S) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (B i) x =
      fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1)) (EuclideanSpace.single i 1))) x := by
    dsimp only [B]
    rw [value_holderEvaluate, hT i hi x,
      OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian _ (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) _)]
    have hc : OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))
        (EuclideanSpace.single k 1) =
        OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))
          (EuclideanSpace.single i 1) := by
      funext y
      exact OAI.Analysis.PDE.Dirichlet.directionalDerivative_comm (hu.of_le (by norm_num)) _ _ y
    rw [hc]
  have hBn (i : I) (hi : i ≠ k) : ‖B i‖ ≤ M :=
    (holderEvaluate_norm_le _ (by simp)).trans (hTn i hi)
  obtain ⟨Tn,hTnval,hTnnorm⟩ := hrecover S (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))
    (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) _) k a A R B hA hAn hB M Q hM hQ hBn hRn hpos heq
  exact ⟨Tn,hTnval,hTnnorm⟩

/-- Tangential third-derivative fields and the twice-normal differentiated
equation recover every fourth derivative, with a uniform coefficient-dependent
bound. In particular, no fourth-derivative Hölder field is assumed in advance. -/
theorem exists_uniform_fourth_holder
    {α μ N : ℝ} (hα : 0 ≤ α) (hμ : 0 < μ) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (S : Set E) (u : E → ℝ), ContDiff ℝ 4 u → ∀ k : I,
      ∀ (a : E → Matrix I I ℝ) (A : I × I → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
        (R : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α) (T : I → OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α),
      (∀ p (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p) x = a x p.1 p.2) →
      (∀ p, ‖A p‖ ≤ N) →
      (∀ i, i ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T i) x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)))) x) →
      ∀ M Q, 0 ≤ M → 0 ≤ Q → (∀ i, i ≠ k → ‖T i‖ ≤ M) → ‖R‖ ≤ Q →
      (∀ x : S, μ ≤ a x k k) →
      (∀ x : S, OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))
          (EuclideanSpace.single k 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) →
      HasFourthHolderBound S α u (C*(M+Q)) := by
  classical
  obtain ⟨C,hC,hrecover⟩ := exists_uniform_normal_third_holder (I := I) hα hμ hN
  let d : ℝ := Fintype.card I
  refine ⟨1+d*(1+C), by dsimp only [d]; positivity, ?_⟩
  intro S u hu k a A R T hA hAn hT M Q hM hQ hTn hRn hpos heq
  obtain ⟨Tn,hTnval,hTnnorm⟩ := hrecover S u hu k a A R T hA hAn hT M Q hM hQ hTn hRn hpos heq
  have hT' : ∀ i, i ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T i) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.basisFun I ℝ i)))) x := by
    simpa only [EuclideanSpace.basisFun_apply] using hT
  have hTnval' : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value Tn x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.basisFun I ℝ k)))) x := by
    simpa only [EuclideanSpace.basisFun_apply] using hTnval
  have hb : HasFourthHolderBound S α u (d*(M+C*(M+Q))) :=
    exists_fourth_holder_of_tangential_thirds
    (EuclideanSpace.basisFun I ℝ) k hα u hu T Tn hT' hTnval'
    hM (mul_nonneg hC.le (add_nonneg hM hQ)) hTn hTnnorm
  apply hb.mono
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  nlinarith [mul_nonneg hd hQ]

end OAI.Analysis.PDE.Elliptic
