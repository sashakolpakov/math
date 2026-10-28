import OAI.Analysis.PDE.Dirichlet.Comparison
import OAI.Analysis.PDE.Dirichlet.Continuity

open Set
open scoped Matrix ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem mooreDet_add_smul_lower {n : ℕ}
    (A R : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosSemidef) (hR : (OAI.LinearAlgebra.Moore.complexify R).PosDef)
    {b : ℝ} (hb : 0 < b) : b ^ n * OAI.LinearAlgebra.Moore.mooreDet n R ≤ OAI.LinearAlgebra.Moore.mooreDet n (A + b • R) := by
  have hbR : (OAI.LinearAlgebra.Moore.complexify (b • R)).PosDef := by
    rw [OAI.LinearAlgebra.Moore.complexify_real_smul]
    exact hR.smul hb
  have h := OAI.LinearAlgebra.Moore.mooreDet_le_of_posSemidef_difference (b • R) (A + b • R) hbR (by simpa using hA)
  simpa only [OAI.LinearAlgebra.Moore.mooreDet_smul] using h

theorem moore_barrier_matrix_posDef {n : ℕ}
    (A R : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosSemidef) (hR : (OAI.LinearAlgebra.Moore.complexify R).PosDef)
    {b : ℝ} (hb : 0 < b) : (OAI.LinearAlgebra.Moore.complexify (A + b • R)).PosDef := by
  rw [OAI.LinearAlgebra.Moore.complexify_add, OAI.LinearAlgebra.Moore.complexify_real_smul]
  exact Matrix.PosDef.posSemidef_add hA (hR.smul hb)

/-- A single sufficiently large multiple works throughout a compact family.
This is the lower-barrier determinant inequality in the continuity method. -/
theorem exists_uniform_large_moore_barrier {X : Type*} [TopologicalSpace X]
    {n : ℕ} (hn : 1 ≤ n) {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    (A R : X → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (F : X → ℝ)
    (hA : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosSemidef)
    (hR : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (R x)).PosDef)
    (hRcont : ContinuousOn (fun x ↦ OAI.LinearAlgebra.Moore.mooreDet n (R x)) K) (hF : ContinuousOn F K) :
    ∃ b : ℝ, 1 ≤ b ∧ ∀ x ∈ K, F x < OAI.LinearAlgebra.Moore.mooreDet n (A x + b • R x) := by
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hKne hRcont
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hKne hF
  let d : ℝ := OAI.LinearAlgebra.Moore.mooreDet n (R y)
  have hd : 0 < d := OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef (R y) (hR y hy)
  let b : ℝ := max 1 ((F z + 1) / d)
  have hb : 1 ≤ b := le_max_left _ _
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hbd : F z < b * d := by
    have h := mul_le_mul_of_nonneg_right (le_max_right 1 ((F z + 1) / d)) hd.le
    change (F z + 1) / d * d ≤ b * d at h
    rw [div_mul_cancel₀ _ hd.ne'] at h
    linarith
  have hbpow : b ≤ b ^ n := le_self_pow₀ hb (by omega)
  refine ⟨b, hb, ?_⟩
  intro x hx
  calc
    F x ≤ F z := hmax hx
    _ < b * d := hbd
    _ ≤ b ^ n * OAI.LinearAlgebra.Moore.mooreDet n (R x) :=
      mul_le_mul hbpow (hmin hx) hd.le (pow_nonneg hbpos.le _)
    _ ≤ OAI.LinearAlgebra.Moore.mooreDet n (A x + b • R x) := mooreDet_add_smul_lower (A x) (R x) (hA x hx) (hR x hx) hbpos

/-- A compact derivative bound makes the singular background determinant
uniformly small after adding a sufficiently small positive multiple. -/
theorem exists_uniform_small_moore_barrier {X : Type*} [TopologicalSpace X]
    {n : ℕ} {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    (A R : X → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (F : X → ℝ)
    (hzero : ∀ x ∈ K, OAI.LinearAlgebra.Moore.mooreDet n (A x) = 0)
    (hF : ContinuousOn F K) (hFpos : ∀ x ∈ K, 0 < F x)
    (hD : ContinuousOn (fun p : X × ℝ ↦
      ‖OAI.LinearAlgebra.Moore.mooreDifferential n (A p.1 + p.2 • R p.1) (R p.1)‖) (K ×ˢ Icc 0 1)) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ ∀ x ∈ K, OAI.LinearAlgebra.Moore.mooreDet n (A x + b • R x) < F x := by
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hKne hF
  obtain ⟨p, hp, hmax⟩ := (hK.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).exists_isMaxOn
    (hKne.prod (nonempty_Icc.mpr zero_le_one)) hD
  let d : ℝ := F y
  let C : ℝ := ‖OAI.LinearAlgebra.Moore.mooreDifferential n (A p.1 + p.2 • R p.1) (R p.1)‖ + 1
  have hd : 0 < d := hFpos y hy
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ x ∈ K, ∀ t ∈ Ico (0 : ℝ) 1,
      ‖OAI.LinearAlgebra.Moore.mooreDifferential n (A x + t • R x) (R x)‖ ≤ C := by
    intro x hx t ht
    have h := hmax (show (x, t) ∈ K ×ˢ Icc 0 1 from ⟨hx, ht.1, ht.2.le⟩)
    exact h.trans (by dsimp [C]; linarith)
  let b : ℝ := min (1 / 2) (d / (2 * (C + 1)))
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hble : b ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hCb : C * b < d := by
    have hbsecond : b ≤ d / (2 * (C + 1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp hbsecond
    nlinarith
  refine ⟨b, hbpos, hble, ?_⟩
  intro x hx
  have hder : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s ↦ OAI.LinearAlgebra.Moore.mooreDet n (A x + s • R x))
        (OAI.LinearAlgebra.Moore.mooreDifferential n (A x + t • R x) (R x)) (Icc (0 : ℝ) 1) t := by
    intro t ht
    exact (OAI.LinearAlgebra.Moore.hasDerivAt_mooreDet_affine (A x) (R x) t).hasDerivWithinAt
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hder (hbound x hx) b ⟨hbpos.le, hble⟩
  simp only [zero_smul, add_zero, hzero x hx, sub_zero, Real.norm_eq_abs] at hmv
  calc
    OAI.LinearAlgebra.Moore.mooreDet n (A x + b • R x) ≤ |OAI.LinearAlgebra.Moore.mooreDet n (A x + b • R x)| := le_abs_self _
    _ ≤ C * b := hmv
    _ < d := hCb
    _ ≤ F x := hmin hx

theorem exists_uniform_moore_barriers {X : Type*} [TopologicalSpace X]
    {n : ℕ} (hn : 1 ≤ n) {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    (A R : X → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (F : X → ℝ)
    (hAc : Continuous A) (hRc : Continuous R) (hF : Continuous F)
    (hA : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosSemidef)
    (hR : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (R x)).PosDef)
    (hzero : ∀ x ∈ K, OAI.LinearAlgebra.Moore.mooreDet n (A x) = 0) (hFpos : ∀ x ∈ K, 0 < F x) :
    ∃ b B : ℝ, 0 < b ∧ b ≤ B ∧ ∀ x ∈ K,
      OAI.LinearAlgebra.Moore.mooreDet n (A x + b • R x) < F x ∧ F x < OAI.LinearAlgebra.Moore.mooreDet n (A x + B • R x) := by
  have hr : ContinuousOn (fun x ↦ OAI.LinearAlgebra.Moore.mooreDet n (R x)) K :=
    ((OAI.LinearAlgebra.Moore.continuous_mooreDet n).comp hRc).continuousOn
  obtain ⟨B, hB, hlarge⟩ := exists_uniform_large_moore_barrier hn hK hKne A R F hA hR hr hF.continuousOn
  obtain ⟨b, hb, hb1, hsmall⟩ := exists_uniform_small_moore_barrier hK hKne A R F hzero
    hF.continuousOn hFpos (continuous_mooreAffineDifferential A R hAc hRc).continuousOn
  exact ⟨b, B, hb, hb1.trans hB, fun x hx ↦ ⟨hsmall x hx, hlarge x hx⟩⟩

/-- Every admissible smooth solution obeys the two defining-function barriers.
The constants are constructed uniformly from the data, not supplied as hypotheses. -/
theorem quaternionic_dirichlet_solution_barriers {n : ℕ} (hn : 1 ≤ n)
    {K : Set (CoordinateSpace n 4)} (hK : IsCompact K) (hKne : K.Nonempty)
    {B₀ r u : CoordinateSpace n 4 → ℝ} (hB₀ : ContDiff ℝ 2 B₀)
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u)
    (F : CoordinateSpace n 4 → ℝ) (hF : Continuous F)
    (hA : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hR : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hzero : ∀ x ∈ K, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hFpos : ∀ x ∈ K, 0 < F x)
    (husol : ∀ x ∈ interior K,
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef)
    (heq : ∀ x ∈ interior K,
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x)
    (hrbd : ∀ x ∈ K, x ∉ interior K → r x = 0)
    (hubd : ∀ x ∈ K, x ∉ interior K → u x = 0) :
    ∃ b B : ℝ, 0 < b ∧ b ≤ B ∧ ∀ x ∈ K, B * r x ≤ u x ∧ u x ≤ b * r x := by
  obtain ⟨b, B, hb, hbB, hbounds⟩ := exists_uniform_moore_barriers hn hK hKne
    (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r) F
    (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hB₀) (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hr)
    hF hA hR hzero hFpos
  have hB : 0 < B := hb.trans_le hbB
  have hlower : ∀ x ∈ K, B₀ x + B • r x ≤ B₀ x + u x := by
    apply quaternionic_dirichlet_comparison hn hK (hB₀.add (hr.const_smul B)) (hB₀.add hu)
    · intro x hx
      rw [quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact moore_barrier_matrix_posDef _ _ (hA x (interior_subset hx))
        (hR x (interior_subset hx)) hB
    · intro x hx
      rw [heq x hx, quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact (hbounds x (interior_subset hx)).2.le
    · intro x hx hxi
      simp [hrbd x hx hxi, hubd x hx hxi]
  have hupper : ∀ x ∈ K, B₀ x + u x ≤ B₀ x + b • r x := by
    apply quaternionic_dirichlet_comparison hn hK (hB₀.add hu) (hB₀.add (hr.const_smul b)) husol
    · intro x hx
      rw [heq x hx, quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact (hbounds x (interior_subset hx)).1.le
    · intro x hx hxi
      simp [hrbd x hx hxi, hubd x hx hxi]
  refine ⟨b, B, hb, hbB, ?_⟩
  intro x hx
  constructor
  · simpa only [smul_eq_mul, add_le_add_iff_left] using hlower x hx
  · simpa only [smul_eq_mul, add_le_add_iff_left] using hupper x hx

end OAI.Analysis.PDE.Dirichlet
