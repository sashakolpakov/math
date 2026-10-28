import OAI.Analysis.PDE.Dirichlet.Barriers

open Set
open scoped ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- The linearized maximum principle requires only positivity of the actual
background matrix; inverses and the sign of the determinant are consequences. -/
theorem moore_maximum_principle_posDef {n : ℕ} (hn : 1 ≤ n)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)} {M : ℝ}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hL : ∀ x ∈ interior K, 0 ≤ mooreLinearization A f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ M) : ∀ x ∈ K, f x ≤ M := by
  classical
  have hi : ∀ x, ∃ C : Matrix (Fin n) (Fin n) (Quaternion ℝ),
      x ∈ interior K → A x * C = 1 ∧ C * A x = 1 := by
    intro x
    by_cases hx : x ∈ interior K
    · obtain ⟨C, hC⟩ := OAI.LinearAlgebra.Moore.exists_quaternion_inverse_of_complexify_posDef (A x) (hA x hx)
      exact ⟨C, fun _ ↦ hC⟩
    · exact ⟨0, fun h ↦ (hx h).elim⟩
  choose C hC using hi
  exact moore_maximum_principle hn hK hf hA
    (fun x hx ↦ (hC x hx).1) (fun x hx ↦ (hC x hx).2)
    (fun x hx ↦ OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef (A x) (hA x hx)) hL hbd

theorem quaternionHessian_const {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (c : ℝ) (x : CoordinateSpace n s) : quaternionHessian e (fun _ ↦ c) x = 0 := by
  unfold quaternionHessian realHessian OAI.Analysis.Calculus.Quaternion.hessianMap
  funext a b
  simp

theorem quaternionHessian_smul {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : CoordinateSpace n s → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : CoordinateSpace n s) :
    quaternionHessian e (fun y ↦ c • f y) x = c • quaternionHessian e f x := by
  simpa only [zero_add, quaternionHessian_const] using
    quaternionHessian_add_smul e (show ContDiff ℝ 2 (fun _ : CoordinateSpace n s ↦ (0 : ℝ)) from contDiff_const) hf c x

theorem mooreLinearization_smul {n : ℕ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    {f : CoordinateSpace n 4 → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : CoordinateSpace n 4) :
    mooreLinearization A (fun y ↦ c • f y) x = c * mooreLinearization A f x := by
  simp only [mooreLinearization, quaternionHessian_smul OAI.Analysis.Calculus.Quaternion.fourSlots hf, OAI.LinearAlgebra.Moore.mooreDifferential_smul]

/-- A quantitative maximum estimate with a defining-function barrier. Applied
to first derivatives, this is the comparison step in the gradient estimate. -/
theorem moore_linearized_barrier_estimate {n : ℕ} (hn : 1 ≤ n)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f r : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)} {M c : ℝ}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f) (hr : ContDiff ℝ 2 r)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hL : ∀ x ∈ interior K, |mooreLinearization A f x| ≤ c * mooreLinearization A r x)
    (hbd : ∀ x ∈ K, x ∉ interior K → |f x| ≤ M)
    (hrbd : ∀ x ∈ K, x ∉ interior K → r x = 0) :
    ∀ x ∈ K, |f x| ≤ M - c * r x := by
  have hp : ∀ x ∈ K, f x + c • r x ≤ M := by
    apply moore_maximum_principle_posDef hn hK (hf.add (hr.const_smul c)) hA
    · intro x hx
      rw [mooreLinearization_add_smul A hf hr]
      have := (abs_le.mp (hL x hx)).1
      linarith
    · intro x hx hxi
      simpa only [hrbd x hx hxi, smul_zero, add_zero] using (le_abs_self (f x)).trans (hbd x hx hxi)
  have hm : ∀ x ∈ K, (-1 : ℝ) • f x + c • r x ≤ M := by
    apply moore_maximum_principle_posDef hn hK ((hf.const_smul (-1 : ℝ)).add (hr.const_smul c)) hA
    · intro x hx
      rw [mooreLinearization_add_smul A (hf.const_smul (-1 : ℝ)) hr,
        mooreLinearization_smul A hf]
      have := (abs_le.mp (hL x hx)).2
      linarith
    · intro x hx hxi
      simpa only [hrbd x hx hxi, smul_zero, add_zero, neg_smul, one_smul]
        using (neg_le_abs (f x)).trans (hbd x hx hxi)
  intro x hx
  have hp' := hp x hx
  have hm' := hm x hx
  simp only [smul_eq_mul] at hp' hm'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A one-sided barrier estimate, used for the pure second derivatives of a
solution after differentiating the concave logarithmic equation. -/
theorem moore_linearized_upper_estimate {n : ℕ} (hn : 1 ≤ n)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f r : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)} {M c : ℝ}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f) (hr : ContDiff ℝ 2 r)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hL : ∀ x ∈ interior K, -c * mooreLinearization A r x ≤ mooreLinearization A f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ M)
    (hrbd : ∀ x ∈ K, x ∉ interior K → r x = 0) :
    ∀ x ∈ K, f x ≤ M - c * r x := by
  have hp : ∀ x ∈ K, f x + c • r x ≤ M := by
    apply moore_maximum_principle_posDef hn hK (hf.add (hr.const_smul c)) hA
    · intro x hx
      rw [mooreLinearization_add_smul A hf hr]
      have := hL x hx
      linarith
    · intro x hx hxi
      simpa only [hrbd x hx hxi, smul_zero, add_zero] using hbd x hx hxi
  intro x hx
  have := hp x hx
  simp only [smul_eq_mul] at this
  linarith

end OAI.Analysis.PDE.Dirichlet
