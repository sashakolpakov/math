import OAI.Analysis.PDE.Dirichlet.AdaptedContinuous
import OAI.Analysis.PDE.Dirichlet.FixedData

open Set Filter
open scoped Topology Matrix Matrix.Norms.Elementwise

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

theorem continuous_realMatrixAction {n : ℕ} :
    Continuous (realMatrixAction (ι := Fin n × Fin 4)) :=
  (Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional

theorem continuous_realRepresentation {X : Type*} [TopologicalSpace X] {n : ℕ}
    {A : X → Matrix (Fin n) (Fin n) Q} (hA : Continuous A) :
    Continuous (fun x ↦ realRepresentation (A x)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply Quaternion.continuous_re.comp
  exact (continuous_const.mul ((continuous_apply j.1).comp
    ((continuous_apply i.1).comp hA))).mul continuous_const

section Family
variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_affineDerivative_family {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    {e z : X → E} {A : X → E →L[ℝ] E}
    (he : Continuous e) (hA : Continuous A) (hz : Continuous z) :
    Continuous (fun x ↦ affineDerivative f (e x) (A x) (z x)) := by
  have hD : Continuous (fderiv ℝ f) :=
    (hf.fderiv_right (m := 0) (by norm_num)).continuous
  exact (hD.comp hz).clm_apply (he.add (hA.clm_apply hz))

theorem continuous_hessian_affineDerivative_family {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {e z v w : X → E} {A : X → E →L[ℝ] E}
    (he : Continuous e) (hA : Continuous A) (hz : Continuous z)
    (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x ↦ fderiv ℝ (fderiv ℝ (affineDerivative f (e x) (A x)))
      (z x) (v x) (w x)) := by
  have hD2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  have hD3 : Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) :=
    (hD2.fderiv_right (m := 0) (by norm_num)).continuous
  simp_rw [hessian_affineDerivative hf]
  exact (((hD3.comp hz).clm_apply hv).clm_apply hw).clm_apply (he.add (hA.clm_apply hz)) |>.add
    (((hD2.continuous.comp hz).clm_apply hv).clm_apply (hA.clm_apply hw)) |>.add
    (((hD2.continuous.comp hz).clm_apply hw).clm_apply (hA.clm_apply hv))

end Family

theorem continuous_quaternionHessian_affineDerivative_family
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    {f : CoordinateSpace n 4 → ℝ} (hf : ContDiff ℝ 3 f)
    {e z : X → CoordinateSpace n 4}
    {A : X → CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4}
    (he : Continuous e) (hA : Continuous A) (hz : Continuous z) :
    Continuous (fun x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (affineDerivative f (e x) (A x)) (z x)) := by
  apply (hessianMatrixCLM OAI.Analysis.Calculus.Quaternion.fourSlots).continuous.comp
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_hessian_affineDerivative_family hf he hA hz continuous_const continuous_const

theorem continuous_realHessian_affineDerivative_family
    {X : Type*} [TopologicalSpace X] {n s : ℕ}
    {f : CoordinateSpace n s → ℝ} (hf : ContDiff ℝ 3 f)
    {e z : X → CoordinateSpace n s}
    {A : X → CoordinateSpace n s →L[ℝ] CoordinateSpace n s}
    (he : Continuous e) (hA : Continuous A) (hz : Continuous z) :
    Continuous (fun x ↦ realHessian (affineDerivative f (e x) (A x)) (z x)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_hessian_affineDerivative_family hf he hA hz continuous_const continuous_const

/-- Uniform real second-derivative control of an actual compact family of affine derivatives. -/
theorem exists_compact_family_affine_hessian_bound
    {P : Type*} [TopologicalSpace P] [CompactSpace P] {n s : ℕ}
    {f : CoordinateSpace n s → ℝ} (hf : ContDiff ℝ 3 f)
    {e : P → CoordinateSpace n s} {A : P → CoordinateSpace n s →L[ℝ] CoordinateSpace n s}
    (he : Continuous e) (hA : Continuous A)
    {S : Set (CoordinateSpace n s)} (hS : IsCompact S) :
    ∃ C : ℝ, 0 < C ∧ ∀ p x, x ∈ S →
      ‖fderiv ℝ (fderiv ℝ (affineDerivative f (e p) (A p))) x‖ ≤ C := by
  have hc : Continuous (fun z : CoordinateSpace n s × P ↦
      ‖realHessian (affineDerivative f (e z.2) (A z.2)) z.1‖) :=
    (continuous_realHessian_affineDerivative_family hf (he.comp continuous_snd)
      (hA.comp continuous_snd) continuous_fst).norm
  obtain ⟨D, hD⟩ := (hS.prod (isCompact_univ : IsCompact (univ : Set P))).bddAbove_image hc.continuousOn
  let B := max D 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨(Fintype.card (Fin n × Fin s) : ℝ) ^ 2 * B + 1, by positivity, ?_⟩
  intro p x hx
  have hbound : ‖realHessian (affineDerivative f (e p) (A p)) x‖ ≤ B := by
    have h := hD (mem_image_of_mem _ (show (x, p) ∈ S ×ˢ (univ : Set P) from ⟨hx, mem_univ _⟩))
    exact h.trans (by dsimp [B]; linarith [le_max_left D 0])
  have helem := (Matrix.norm_le_iff hB.le).mp hbound
  have hnorm := hessian_norm_le_of_entry_bound (affineDerivative f (e p) (A p)) x hB.le
    (by simpa only [Real.norm_eq_abs] using helem)
  linarith

theorem exists_compact_family_affine_size_bound
    {P : Type*} [TopologicalSpace P] [CompactSpace P] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e : P → E} {A : P → E →L[ℝ] E} (he : Continuous e) (hA : Continuous A)
    {S : Set E} (hS : IsCompact S) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ, ∀ G : ℝ, 0 ≤ G →
      (∀ x ∈ S, ‖fderiv ℝ u x‖ ≤ G) → ∀ p x, x ∈ S →
        |affineDerivative u (e p) (A p) x| ≤ G * C := by
  have hc : Continuous (fun z : E × P ↦ ‖e z.2 + A z.2 z.1‖) :=
    ((he.comp continuous_snd).add ((hA.comp continuous_snd).clm_apply continuous_fst)).norm
  obtain ⟨D, hD⟩ := (hS.prod (isCompact_univ : IsCompact (univ : Set P))).bddAbove_image hc.continuousOn
  let C := max D 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u G hG hgrad p x hx
  have hfield : ‖e p + A p x‖ ≤ C := by
    have h := hD (mem_image_of_mem _ (show (x, p) ∈ S ×ˢ (univ : Set P) from ⟨hx, mem_univ _⟩))
    exact h.trans (by dsimp [C]; linarith [le_max_left D 0])
  calc
    |affineDerivative u (e p) (A p) x| = ‖fderiv ℝ u x (e p + A p x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ u x‖ * ‖e p + A p x‖ := (fderiv ℝ u x).le_opNorm _
    _ ≤ G * C := mul_le_mul (hgrad x hx) hfield (norm_nonneg _) hG

end OAI.Analysis.PDE.Dirichlet
