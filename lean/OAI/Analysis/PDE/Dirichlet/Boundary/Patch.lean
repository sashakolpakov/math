import OAI.Analysis.PDE.Dirichlet.LocalBarrier
import OAI.Analysis.PDE.Dirichlet.Boundary.Slope

open Set Filter Metric
open scoped Topology ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine local sublevel patch, including its artificial spherical boundary. -/
def sublevelPatch (r : E → ℝ) (R : ℝ) : Set E :=
  {x | r x ≤ 0} ∩ closedBall 0 R

omit [NormedSpace ℝ E] in
theorem isCompact_sublevelPatch [ProperSpace E] {r : E → ℝ} (hr : Continuous r) (R : ℝ) :
    IsCompact (sublevelPatch r R) := by
  apply (isCompact_closedBall (0 : E) R).of_isClosed_subset
    ((isClosed_le hr continuous_const).inter isClosed_closedBall)
  exact fun _ h ↦ h.2

omit [NormedSpace ℝ E] in
theorem mem_interior_sublevelPatch {r : E → ℝ} (hr : Continuous r)
    {R : ℝ} {x : E} (hrx : r x < 0) (hx : ‖x‖ < R) :
    x ∈ interior (sublevelPatch r R) := by
  apply mem_interior_iff_mem_nhds.mpr
  have ho : IsOpen ({y | r y < 0} ∩ ball (0 : E) R) :=
    (isOpen_lt hr continuous_const).inter isOpen_ball
  have hm : x ∈ {y | r y < 0} ∩ ball (0 : E) R := ⟨hrx, by simpa using hx⟩
  apply Filter.mem_of_superset (ho.mem_nhds hm)
  intro y hy
  have hry : r y < 0 := hy.1
  exact ⟨hry.le, ball_subset_closedBall hy.2⟩

omit [NormedSpace ℝ E] in
theorem sublevelPatch_boundary_cases {r : E → ℝ} (hr : Continuous r)
    {R : ℝ} {x : E} (hx : x ∈ sublevelPatch r R)
    (hxi : x ∉ interior (sublevelPatch r R)) : r x = 0 ∨ ‖x‖ = R := by
  by_cases h : r x = 0
  · exact Or.inl h
  right
  by_contra hn
  have hnorm : ‖x‖ ≤ R := by simpa using hx.2
  exact hxi (mem_interior_sublevelPatch hr (lt_of_le_of_ne hx.1 h)
    (lt_of_le_of_ne hnorm hn))

omit [NormedSpace ℝ E] in
theorem eventually_in_sublevelPatch {r : E → ℝ} {R : ℝ} (hR : 0 < R) :
    ∀ᶠ y in 𝓝 (0 : E), r y < 0 → y ∈ sublevelPatch r R := by
  filter_upwards [ball_mem_nhds (0 : E) hR] with y hy
  exact fun hry ↦ ⟨hry.le, ball_subset_closedBall hy⟩

omit [NormedSpace ℝ E] in
/-- The true boundary uses quadratic vanishing; the artificial spherical
boundary uses only a zeroth-order bound for the differentiated solution. -/
theorem quadratic_barrier_patch_boundary {r f : E → ℝ} {R C D c : ℝ}
    (hr : Continuous r) (hR : 0 < R) (hC : 0 ≤ C) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hlevel : ∀ x ∈ sublevelPatch r R, r x = 0 → |f x| ≤ C * ‖x‖ ^ 2)
    (hsize : ∀ x ∈ sublevelPatch r R, |f x| ≤ D) :
    ∀ x ∈ sublevelPatch r R, x ∉ interior (sublevelPatch r R) →
      |f x| ≤ (C + D / R ^ 2) * ‖x‖ ^ 2 - c * r x := by
  intro x hx hxi
  have hrad : 0 < R ^ 2 := sq_pos_of_pos hR
  have hDC : 0 ≤ D / R ^ 2 := div_nonneg hD hrad.le
  have hrterm : c * r x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hx.1
  rcases sublevelPatch_boundary_cases hr hx hxi with hrx | hnorm
  · have h := hlevel x hx hrx
    have hm : C * ‖x‖ ^ 2 ≤ (C + D / R ^ 2) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hDC) (sq_nonneg ‖x‖)
    exact (h.trans hm).trans (by linarith)
  · have h := hsize x hx
    have hcancel : (D / R ^ 2) * R ^ 2 = D := div_mul_cancel₀ _ hrad.ne'
    have hpos : 0 ≤ C * R ^ 2 := mul_nonneg hC hrad.le
    rw [hnorm]
    nlinarith

/-- The maximum principle on the actual local patch, with its boundary
inequality discharged from the two geometrically distinct boundary pieces. -/
theorem moore_quadratic_estimate_on_patch {n : ℕ} (hn : 1 ≤ n)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f r : CoordinateSpace n 4 → ℝ} {R C D F r₀ : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hD : 0 ≤ D) (hF : 0 ≤ F) (hr₀ : 0 < r₀)
    (hf : ContDiff ℝ 2 f) (hr : ContDiff ℝ 2 r)
    (hA : ∀ x ∈ interior (sublevelPatch r R), (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hconvex : ∀ x ∈ interior (sublevelPatch r R),
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef)
    (hL : ∀ x ∈ interior (sublevelPatch r R),
      |mooreLinearization A f x| ≤ F * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) 1)
    (hlevel : ∀ x ∈ sublevelPatch r R, r x = 0 → |f x| ≤ C * ‖x‖ ^ 2)
    (hsize : ∀ x ∈ sublevelPatch r R, |f x| ≤ D) :
    ∀ x ∈ sublevelPatch r R, |f x| ≤ (C + D / R ^ 2) * ‖x‖ ^ 2 -
      ((F + 8 * (C + D / R ^ 2)) / r₀) * r x := by
  have hM : 0 ≤ C + D / R ^ 2 := add_nonneg hC (div_nonneg hD (sq_nonneg _))
  apply moore_linearized_quadratic_barrier hn hF hM hr₀
    (isCompact_sublevelPatch hr.continuous R) hf hr hA hconvex hL
  exact quadratic_barrier_patch_boundary hr.continuous hR hC hD
    (div_nonneg (by positivity) hr₀.le) hlevel hsize

/-- A genuine normal-tangential second-derivative estimate. The boundary
inputs involve only the adapted first derivative of the solution, and the
operator input is its actual trace-weighted forcing estimate. -/
theorem boundary_mixed_hessian_on_patch {n : ℕ} (hn : 1 ≤ n)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {u r : CoordinateSpace n 4 → ℝ} {e v : CoordinateSpace n 4}
    {B : CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4} {a R C D F r₀ : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hD : 0 ≤ D) (hF : 0 ≤ F) (hr₀ : 0 < r₀)
    (hu : ContDiff ℝ 3 u) (hr : ContDiff ℝ 2 r) (hr0 : r 0 = 0)
    (hfactor : fderiv ℝ u 0 = a • fderiv ℝ r 0)
    (he : fderiv ℝ r 0 e = 0) (hBv : fderiv ℝ r 0 (B v) = 0)
    (hinward : fderiv ℝ r 0 v < 0)
    (hA : ∀ x ∈ interior (sublevelPatch r R), (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hconvex : ∀ x ∈ interior (sublevelPatch r R),
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef)
    (hL : ∀ x ∈ interior (sublevelPatch r R),
      |mooreLinearization A (affineDerivative u e B) x| ≤ F * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) 1)
    (hlevel : ∀ x ∈ sublevelPatch r R, r x = 0 →
      |affineDerivative u e B x| ≤ C * ‖x‖ ^ 2)
    (hsize : ∀ x ∈ sublevelPatch r R, |affineDerivative u e B x| ≤ D) :
    |fderiv ℝ (fderiv ℝ u) 0 v e| ≤
      -((F + 8 * (C + D / R ^ 2)) / r₀) * fderiv ℝ r 0 v := by
  have hbound := moore_quadratic_estimate_on_patch hn hR hC hD hF hr₀
    (contDiff_affineDerivative hu (by norm_num) e B) hr hA hconvex hL hlevel hsize
  apply boundary_mixed_hessian_of_affine_barrier (hu.of_le (by norm_num))
    ((hr.differentiable (by norm_num)) 0) hr0 hfactor he hBv hinward
  filter_upwards [eventually_in_sublevelPatch (r := r) hR] with y hy
  exact fun hry ↦ hbound y (hy hry)

end OAI.Analysis.PDE.Dirichlet
