import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Jet

open Set
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

@[instance_reducible]
private def fourthTanHolderNorm (X Y : Type*) [MetricSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (α : ℝ) : Norm (OAI.Analysis.Normed.Function.Holder.HolderMap X Y α) :=
  inferInstance

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I
local instance fourthTanFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthTanFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthTanSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTanSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTanThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTanThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTanFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTanFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTanNorm {S : Set E} {α : ℝ} :
    Norm (OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α) :=
  fourthTanHolderNorm _ _ α

/-- Only the twice-tangential Hessians need separate Schauder estimates.
Two applications of normal recovery give the full fourth derivative with
a uniform bound, using the actual twice-differentiated equations. -/
theorem exists_uniform_fourth_holder_of_double_tangential
    {α μ N : ℝ} (hα : 0 ≤ α) (hμ : 0 < μ) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (S : Set E) (u : E → ℝ), ContDiff ℝ 4 u → ∀ k : I,
      ∀ (a : E → Matrix I I ℝ) (A : I × I → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
        (R : I → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
        (B : I × I → OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α),
      (∀ p (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p) x = a x p.1 p.2) →
      (∀ p, ‖A p‖ ≤ N) →
      (∀ i, i ≠ k → ∀ j, j ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value (B (i,j)) x =
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative
          (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1))) x) →
      ∀ M Q, 0 ≤ M → 0 ≤ Q →
      (∀ i, i ≠ k → ∀ j, j ≠ k → ‖B (i,j)‖ ≤ M) → (∀ i, ‖R i‖ ≤ Q) →
      (∀ x : S, μ ≤ a x k k) →
      (∀ i (x : S), OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))
          (EuclideanSpace.single k 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (R i) x) →
      HasFourthHolderBound S α u (C*(M+Q)) := by
  classical
  obtain ⟨C₃,hC₃,hthird⟩ := exists_uniform_third_holder (I := I) hα hμ hN
  obtain ⟨C₄,hC₄,hfourth⟩ := exists_uniform_fourth_holder (I := I) hα hμ hN
  refine ⟨C₄*(C₃+1), mul_pos hC₄ (by linarith), ?_⟩
  intro S u hu k a A R B hA hAn hB M Q hM hQ hBn hRn hpos heq
  have hbound : 0 ≤ C₃*(M+Q) := mul_nonneg hC₃.le (add_nonneg hM hQ)
  have hex (i : I) : ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (i ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)))) x) ∧
      ‖T‖ ≤ C₃*(M+Q) := by
    by_cases hi : i = k
    · exact ⟨0, fun h => (h hi).elim, by simpa only [norm_zero] using hbound⟩
    · obtain ⟨T,hT,hTn⟩ := hthird S (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))
        (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) _) k a A (R i) (fun j => B (i,j))
        hA hAn (hB i hi) M Q hM hQ (hBn i hi) (hRn i) hpos (heq i)
      exact ⟨T, fun _ => hT, hTn⟩
  choose T hT hTn using hex
  have hW := hfourth S u hu k a A (R k) T hA hAn hT
    (C₃*(M+Q)) Q hbound hQ (fun i _ => hTn i) (hRn k) hpos (heq k)
  apply hW.mono
  have hinner : C₃*(M+Q)+Q ≤ (C₃+1)*(M+Q) := by nlinarith
  calc
    C₄*(C₃*(M+Q)+Q) ≤ C₄*((C₃+1)*(M+Q)) := mul_le_mul_of_nonneg_left hinner hC₄.le
    _ = (C₄*(C₃+1))*(M+Q) := by ring

end OAI.Analysis.PDE.Elliptic
