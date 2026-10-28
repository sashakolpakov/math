import OAI.Analysis.PDE.Dirichlet.CoerciveData

open Set
open scoped ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- Absolute comparison with a nonconstant supersolution. -/
theorem moore_linearized_absolute_comparison {n : ℕ} (hn : 1 ≤ n)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f w : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f) (hw : ContDiff ℝ 2 w)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hL : ∀ x ∈ interior K, |mooreLinearization A f x| ≤ -mooreLinearization A w x)
    (hbd : ∀ x ∈ K, x ∉ interior K → |f x| ≤ w x) :
    ∀ x ∈ K, |f x| ≤ w x := by
  have hp : ∀ x ∈ K, f x + (-1 : ℝ) • w x ≤ 0 := by
    apply moore_maximum_principle_posDef hn hK (hf.add (hw.const_smul (-1 : ℝ))) hA
    · intro x hx
      rw [mooreLinearization_add_smul A hf hw]
      have := (abs_le.mp (hL x hx)).1
      linarith
    · intro x hx hxi
      have := (le_abs_self (f x)).trans (hbd x hx hxi)
      simp only [smul_eq_mul]
      linarith
  have hm : ∀ x ∈ K, (-1 : ℝ) • f x + (-1 : ℝ) • w x ≤ 0 := by
    apply moore_maximum_principle_posDef hn hK
      ((hf.const_smul (-1 : ℝ)).add (hw.const_smul (-1 : ℝ))) hA
    · intro x hx
      rw [mooreLinearization_add_smul A (hf.const_smul (-1 : ℝ)) hw,
        mooreLinearization_smul A hf]
      have := (abs_le.mp (hL x hx)).2
      linarith
    · intro x hx hxi
      have := (neg_le_abs (f x)).trans (hbd x hx hxi)
      simp only [smul_eq_mul]
      linarith
  intro x hx
  have hp' := hp x hx
  have hm' := hm x hx
  simp only [smul_eq_mul] at hp' hm'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem mooreDifferential_ge_identity {n : ℕ}
    (A R : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef)
    (r₀ : ℝ)
    (hR : (OAI.LinearAlgebra.Moore.complexify (R - r₀ • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef) :
    r₀ * OAI.LinearAlgebra.Moore.mooreDifferential n A 1 ≤ OAI.LinearAlgebra.Moore.mooreDifferential n A R := by
  have hpos := OAI.LinearAlgebra.Moore.mooreDifferential_nonneg_of_posDef A (R - r₀ • 1) hA hR
  have hsplit : OAI.LinearAlgebra.Moore.mooreDifferential n A R =
      OAI.LinearAlgebra.Moore.mooreDifferential n A (R - r₀ • 1) + r₀ * OAI.LinearAlgebra.Moore.mooreDifferential n A 1 := by
    calc
      _ = OAI.LinearAlgebra.Moore.mooreDifferential n A ((R - r₀ • 1) + r₀ • 1) := by rw [sub_add_cancel]
      _ = _ := by rw [OAI.LinearAlgebra.Moore.mooreDifferential_add, OAI.LinearAlgebra.Moore.mooreDifferential_smul]
  linarith

/-- The local mixed-derivative barrier. Its constants require only strict
convexity of the fixed defining function and a trace-weighted forcing bound. -/
theorem moore_linearized_quadratic_barrier {n : ℕ} (hn : 1 ≤ n)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f r : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)}
    {C M r₀ : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hr₀ : 0 < r₀)
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f) (hr : ContDiff ℝ 2 r)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hR : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x -
      r₀ • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef)
    (hL : ∀ x ∈ interior K, |mooreLinearization A f x| ≤ C * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) 1)
    (hbd : ∀ x ∈ K, x ∉ interior K →
      |f x| ≤ M * ‖x‖ ^ 2 - ((C + 8 * M) / r₀) * r x) :
    ∀ x ∈ K, |f x| ≤ M * ‖x‖ ^ 2 - ((C + 8 * M) / r₀) * r x := by
  let c := (C + 8 * M) / r₀
  have hc : 0 ≤ c := div_nonneg (by positivity) hr₀.le
  have hcr : c * r₀ = C + 8 * M := div_mul_cancel₀ _ hr₀.ne'
  let w : CoordinateSpace n 4 → ℝ := fun x ↦ M • ‖x‖ ^ 2 + (-c) • r x
  have hq : ContDiff ℝ 2 (fun x : CoordinateSpace n 4 ↦ ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hw : ContDiff ℝ 2 w := (hq.const_smul M).add (hr.const_smul (-c))
  have hresult := moore_linearized_absolute_comparison hn hK hf hw hA
    (fun x hx ↦ ?_) (fun x hx hxi ↦ ?_)
  · simpa only [w, c, smul_eq_mul, neg_mul, ← sub_eq_add_neg] using hresult
  · have hrLower := mooreDifferential_ge_identity (A x) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)
      (hA x hx) r₀ (hR x hx)
    have hscaled := mul_le_mul_of_nonneg_left hrLower hc
    have hcancel : c * (r₀ * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) 1) =
        (C + 8 * M) * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) 1 := by rw [← mul_assoc, hcr]
    rw [hcancel] at hscaled
    have hwL : mooreLinearization A w x =
        M * (8 * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) 1) - c * mooreLinearization A r x := by
      rw [show w = (fun y ↦ M • ‖y‖ ^ 2 + (-c) • r y) from rfl,
        mooreLinearization_add_smul A (hq.const_smul M) hr,
        mooreLinearization_smul A hq]
      simp only [mooreLinearization, quaternionHessian_four_norm_sq, OAI.LinearAlgebra.Moore.mooreDifferential_smul]
      ring
    rw [hwL]
    have hforce := hL x hx
    change (C + 8 * M) * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) 1 ≤ c * mooreLinearization A r x at hscaled
    nlinarith
  · simpa only [w, c, smul_eq_mul, neg_mul, ← sub_eq_add_neg] using hbd x hx hxi

end OAI.Analysis.PDE.Dirichlet
