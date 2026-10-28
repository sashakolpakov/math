import OAI.Analysis.PDE.Elliptic.Boundary.Third.Schauder

/-! The full third derivative as an actual Hölder field, reconstructed from
tangential Schauder jets and the normal differentiated equation. -/

noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {I : Type*} [Fintype I] [DecidableEq I]

local instance thirdJetFirstGroup : NormedAddCommGroup
    (EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance thirdJetFirstSpace : NormedSpace ℝ
    (EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance thirdJetSecondGroup : NormedAddCommGroup
    (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance thirdJetSecondSpace : NormedSpace ℝ
    (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance

theorem exists_third_holder_of_tangent_and_equation
    {S : Set (EuclideanSpace ℝ I)} {α : ℝ} (hα : 0 ≤ α)
    {u : EuclideanSpace ℝ I → ℝ} (hu : ContDiff ℝ 3 u) (k : I)
    (a : EuclideanSpace ℝ I → Matrix I I ℝ)
    (A : I × I → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α) (R : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
    (B : I → OAI.Analysis.Normed.Function.Holder.HolderMap S (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) α)
    (hA : ∀ p (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p) x = a x p.1 p.2)
    (hB : ∀ i, i ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value (B i) x =
      fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x)
    {M μ : ℝ} (hM : 0 ≤ M) (hμ : 0 < μ)
    (hBn : ∀ i, i ≠ k → ‖B i‖ ≤ M) (hpos : ∀ x : S, μ ≤ a x k k)
    (heq : ∀ x : S, OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a
      (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) :
    let N := 2 * (μ⁻¹ + (μ*μ)⁻¹ * ‖A (k,k)‖) *
      (‖R‖ + ∑ p ∈ (Finset.univ : Finset (I × I)).erase (k,k), 2 * ‖A p‖ * M)
    ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap S
        (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) α,
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) ∧
      ‖T‖ ≤ (Fintype.card I : ℝ)^3 * (M+N) := by
  classical
  dsimp only
  let P (p : I × I) : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α :=
    holderEvaluate (holderEvaluate (B (if p.1 = k then p.2 else p.1))
      (EuclideanSpace.single (if p.1 = k then k else p.2) 1)) (EuclideanSpace.single k 1)
  have hP (p) (hp : p ≠ (k,k)) (x : S) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (P p) x = tangentThirdEntry u k p.1 p.2 x := by
    have hi := tangentThirdEntry_uses_tangent k p.1 p.2 hp
    simp only [P, value_holderEvaluate, hB _ hi, tangentThirdEntry]
    split_ifs <;> rfl
  have hPn (p) (hp : p ≠ (k,k)) : ‖P p‖ ≤ M := by
    apply (holderEvaluate_norm_le _ (by simp)).trans
    apply (holderEvaluate_norm_le _ (by simp)).trans
    exact hBn _ (tangentThirdEntry_uses_tangent k p.1 p.2 hp)
  obtain ⟨H, hH, hHn⟩ := exists_pure_normal_third_holder hα hu k a A P R hA hP hμ hpos heq
  let N := 2 * (μ⁻¹ + (μ*μ)⁻¹ * ‖A (k,k)‖) *
    (‖R‖ + ∑ p ∈ (Finset.univ : Finset (I × I)).erase (k,k), 2 * ‖A p‖ * M)
  have hHn' : ‖H‖ ≤ N := by
    apply hHn.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (hPn p (Finset.mem_erase.mp hp).1) (by positivity)
  have hN : 0 ≤ N := (norm_nonneg H).trans hHn'
  let C := (Fintype.card I : ℝ)^3 * (M+N)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hb (x : S) : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C := by
    apply third_norm_le_of_tangential_and_normal hu k x hM hN
    · intro i hi
      rw [← hB i hi x]
      exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le _ _).trans (hBn i hi)
    · rw [← hH x, ← Real.norm_eq_abs]
      exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le _ _).trans hHn'
  have hh (x y : S) :
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
        C * dist x y ^ α := by
    simpa only [Subtype.dist_eq, dist_eq_norm, C, N] using
      third_holder_of_tangent_and_equation hα hu k a A R B hA hB hM hμ hBn hpos heq x y
  have hc : Continuous (fun x : S => fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) := by
    have hd₁ : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
    have hd : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
      hd₁.fderiv_right (by norm_num)
    exact (hd.continuous_fderiv one_ne_zero).comp continuous_subtype_val
  let T : S →ᵇ (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ]
      EuclideanSpace ℝ I →L[ℝ] ℝ) :=
    BoundedContinuousFunction.ofNormedAddCommGroup _ hc C hb
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα T hh, fun _ => rfl, ?_⟩
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα T hC hh).trans
    (max_le (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hC hb) le_rfl)

/-- A uniform linear bound, with its constant chosen from coefficient bounds
before the tangential derivative fields and the source. -/
theorem exists_uniform_third_holder
    {α : ℝ} (hα : 0 ≤ α)
    {μ N : ℝ} (hμ : 0 < μ) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (S : Set (EuclideanSpace ℝ I))
      (u : EuclideanSpace ℝ I → ℝ), ContDiff ℝ 3 u → ∀ k : I,
      ∀ (a : EuclideanSpace ℝ I → Matrix I I ℝ)
        (A : I × I → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α) (R : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
        (B : I → OAI.Analysis.Normed.Function.Holder.HolderMap S (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) α),
      (∀ p (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p) x = a x p.1 p.2) →
      (∀ p, ‖A p‖ ≤ N) →
      (∀ i, i ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value (B i) x =
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x) →
      ∀ M Q, 0 ≤ M → 0 ≤ Q → (∀ i, i ≠ k → ‖B i‖ ≤ M) → ‖R‖ ≤ Q →
      (∀ x : S, μ ≤ a x k k) →
      (∀ x : S, OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) →
      ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap S
          (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) α,
        (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) ∧
        ‖T‖ ≤ C*(M+Q) := by
  classical
  let d : ℝ := Fintype.card I
  let P := 2*(μ⁻¹+(μ*μ)⁻¹*N)
  let C := 1+d^3*(1+P*(1+2*d^2*N))
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro S u hu k a A R B hA hAn hB M Q hM hQ hBn hRn hpos heq
  obtain ⟨T, hT, hTn⟩ := exists_third_holder_of_tangent_and_equation
    hα hu k a A R B hA hB hM hμ hBn hpos heq
  refine ⟨T, hT, hTn.trans ?_⟩
  have hs : (∑ p ∈ (Finset.univ : Finset (I × I)).erase (k,k), 2*‖A p‖*M) ≤
      d^2*(2*N*M) := by
    calc
      _ ≤ ∑ _p ∈ (Finset.univ : Finset (I × I)).erase (k,k), 2*N*M := by
        apply Finset.sum_le_sum
        intro p hp
        gcongr
        exact hAn p
      _ ≤ ∑ _p : I × I, 2*N*M :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => by positivity)
      _ = d^2*(2*N*M) := by simp [d, pow_two]
  have hp : 2*(μ⁻¹+(μ*μ)⁻¹*‖A (k,k)‖) ≤ P := by
    dsimp only [P]
    gcongr
    exact hAn (k,k)
  calc
    _ ≤ d^3*(M+P*(Q+d^2*(2*N*M))) := by
      change d^3 * _ ≤ _
      gcongr
    _ ≤ C*(M+Q) := by
      dsimp only [C]
      nlinarith [mul_nonneg (pow_nonneg hd 3) hQ,
        mul_nonneg (pow_nonneg hd 3) (mul_nonneg hP hM),
        mul_nonneg (pow_nonneg hd 3)
          (mul_nonneg hP (mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*d^2) hN) hQ))]

end OAI.Analysis.PDE.Elliptic
