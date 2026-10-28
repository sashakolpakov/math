import OAI.LinearAlgebra.Moore.Form

/-! Maximum principles for the actual linearized quaternionic Monge–Ampère operator. -/

open Filter Set
open scoped Topology Matrix ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- The actual logarithmic derivative in the Dirichlet continuity method. -/
theorem hasDerivAt_log_mooreDet_path {n : ℕ}
    (A : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (D C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ)
    (h : ∀ i j, HasDerivAt (fun s ↦ A s i j) (D i j) t)
    (hA : (A t).IsHermitian) (hD : D.IsHermitian)
    (hAC : A t * C = 1) (hCA : C * A t = 1) (hdet : OAI.LinearAlgebra.Moore.mooreDet n (A t) ≠ 0) :
    HasDerivAt (fun s ↦ Real.log (OAI.LinearAlgebra.Moore.mooreDet n (A s))) (∑ i, ((C * D) i i).re) t := by
  have hd := (OAI.LinearAlgebra.Moore.hasDerivAt_mooreDet_path n A D t h).log hdet
  rw [OAI.LinearAlgebra.Moore.mooreDifferential_inverse n (A t) D C hA hD hAC hCA] at hd
  simpa only [mul_div_cancel_left₀ _ hdet] using hd

def mooreLinearization {n : ℕ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (f : CoordinateSpace n 4 → ℝ) (x : CoordinateSpace n 4) : ℝ :=
  OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)

theorem mooreLinearization_add_smul {n : ℕ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    {f g : CoordinateSpace n 4 → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (c : ℝ) (x : CoordinateSpace n 4) :
    mooreLinearization A (fun y ↦ f y + c • g y) x =
      mooreLinearization A f x + c * mooreLinearization A g x := by
  simp only [mooreLinearization, quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hf hg,
    OAI.LinearAlgebra.Moore.mooreDifferential_add, OAI.LinearAlgebra.Moore.mooreDifferential_smul]

theorem mooreLinearization_nonpos_of_localMax {n : ℕ}
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f : CoordinateSpace n 4 → ℝ} {x : CoordinateSpace n 4}
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef) (hAC : A x * C = 1) (hCA : C * A x = 1)
    (hdet : 0 ≤ OAI.LinearAlgebra.Moore.mooreDet n (A x)) (hf : ContDiff ℝ 2 f) (hmax : IsLocalMax f x) :
    mooreLinearization A f x ≤ 0 := by
  have hH := OAI.LinearAlgebra.Moore.complexify_hessianMap_posSemidef OAI.Analysis.Calculus.Quaternion.fourSlots
    (realHessian_neg_posSemidef_of_localMax hf hmax)
  have h := OAI.LinearAlgebra.Moore.mooreDifferential_nonneg n (A x) _ C hA hH hAC hCA hdet
  have hn : OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (-realHessian f x) =
      (-1 : ℝ) • quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x := by
    rw [← neg_one_smul ℝ (realHessian f x), OAI.Analysis.Calculus.Quaternion.hessianMap_smul]
    rfl
  rw [hn, OAI.LinearAlgebra.Moore.mooreDifferential_smul] at h
  unfold mooreLinearization
  linarith

theorem mooreDifferential_one_pos {n : ℕ} (hn : 1 ≤ n)
    (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hAC : A * C = 1) (hCA : C * A = 1)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n A) : 0 < OAI.LinearAlgebra.Moore.mooreDifferential n A 1 := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hC := OAI.LinearAlgebra.Moore.complexify_inverse_posDef n A C hA hAC
  have ht := (Complex.pos_iff.mp hC.trace_pos).1
  rw [OAI.LinearAlgebra.Moore.complexify_trace_real] at ht
  rw [OAI.LinearAlgebra.Moore.mooreDifferential_inverse n A 1 C (OAI.LinearAlgebra.Moore.isHermitian_of_complexify hA.isHermitian)
    (by simp) hAC hCA, Matrix.mul_one]
  exact mul_pos hdet (by linarith)

theorem mooreLinearization_norm_sq_pos {n : ℕ} (hn : 1 ≤ n)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (x : CoordinateSpace n 4) (C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef) (hAC : A x * C = 1) (hCA : C * A x = 1)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n (A x)) :
    0 < mooreLinearization A (fun y ↦ ‖y‖ ^ 2) x := by
  rw [mooreLinearization, quaternionHessian_four_norm_sq, OAI.LinearAlgebra.Moore.mooreDifferential_smul]
  exact mul_pos (by norm_num) (mooreDifferential_one_pos hn (A x) C hA hAC hCA hdet)

/-- Strict comparison uses the Hessian at an actual attained maximum. -/
theorem moore_strict_maximum_principle {n : ℕ}
    {A C : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)} {M : ℝ}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hAC : ∀ x ∈ interior K, A x * C x = 1)
    (hCA : ∀ x ∈ interior K, C x * A x = 1)
    (hdet : ∀ x ∈ interior K, 0 ≤ OAI.LinearAlgebra.Moore.mooreDet n (A x))
    (hL : ∀ x ∈ interior K, 0 < mooreLinearization A f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ M) : ∀ x ∈ K, f x ≤ M := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hf.continuous.continuousOn
  by_cases hyi : y ∈ interior K
  · have hlocal := hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hyi)
    have hnonpos := mooreLinearization_nonpos_of_localMax (C y)
      (hA y hyi) (hAC y hyi) (hCA y hyi) (hdet y hyi) hf hlocal
    exact False.elim (not_lt_of_ge hnonpos (hL y hyi))
  · exact (hmax hx).trans (hbd y hy hyi)

/-- Weak comparison for the linearized Moore determinant, with its genuine
quadratic barrier. No coefficient regularity assumption is needed. -/
theorem moore_maximum_principle {n : ℕ} (hn : 1 ≤ n)
    {A C : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)} {M : ℝ}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hAC : ∀ x ∈ interior K, A x * C x = 1)
    (hCA : ∀ x ∈ interior K, C x * A x = 1)
    (hdet : ∀ x ∈ interior K, 0 < OAI.LinearAlgebra.Moore.mooreDet n (A x))
    (hL : ∀ x ∈ interior K, 0 ≤ mooreLinearization A f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ M) : ∀ x ∈ K, f x ≤ M := by
  intro x hx
  let b : CoordinateSpace n 4 → ℝ := fun y ↦ ‖y‖ ^ 2
  have hb : ContDiff ℝ 2 b := contDiff_norm_sq ℝ
  obtain ⟨z, hz, hbmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hb.continuous.continuousOn
  have hε (ε : ℝ) (hε : 0 < ε) : f x + ε * b x ≤ M + ε * b z := by
    apply moore_strict_maximum_principle hK (hf.add (hb.const_smul ε)) hA hAC hCA
      (fun y hy ↦ (hdet y hy).le) ?_ ?_ x hx
    · intro y hy
      rw [mooreLinearization_add_smul A hf hb]
      exact add_pos_of_nonneg_of_pos (hL y hy) (mul_pos hε
        (mooreLinearization_norm_sq_pos hn y (C y) (hA y hy) (hAC y hy) (hCA y hy) (hdet y hy)))
    · intro y hy hyi
      exact add_le_add (hbd y hy hyi) (mul_le_mul_of_nonneg_left (hbmax hy) hε.le)
  have ht : Tendsto (fun ε : ℝ ↦ f x + ε * b x - (M + ε * b z))
      (𝓝[>] 0) (𝓝 (f x - M)) := by
    have hc : Continuous (fun ε : ℝ ↦ f x + ε * b x - (M + ε * b z)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ ε : ℝ in 𝓝[>] 0, f x + ε * b x - (M + ε * b z) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hpos
    exact sub_nonpos.mpr (hε ε hpos)
  have := le_of_tendsto ht hle
  linarith

theorem moore_dirichlet_comparison {n : ℕ} (hn : 1 ≤ n)
    {A C : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f g : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hAC : ∀ x ∈ interior K, A x * C x = 1)
    (hCA : ∀ x ∈ interior K, C x * A x = 1)
    (hdet : ∀ x ∈ interior K, 0 < OAI.LinearAlgebra.Moore.mooreDet n (A x))
    (hL : ∀ x ∈ interior K, mooreLinearization A g x ≤ mooreLinearization A f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ g x) : ∀ x ∈ K, f x ≤ g x := by
  have hd : ∀ x ∈ K, (fun y ↦ f y + (-1 : ℝ) • g y) x ≤ 0 := by
    apply moore_maximum_principle hn hK (hf.add (hg.const_smul (-1 : ℝ))) hA hAC hCA hdet
    · intro x hx
      rw [mooreLinearization_add_smul A hf hg]
      linarith [hL x hx]
    · intro x hx hxi
      simpa only [neg_smul, one_smul, ← sub_eq_add_neg, sub_nonpos] using hbd x hx hxi
  intro x hx
  simpa only [neg_smul, one_smul, ← sub_eq_add_neg, sub_nonpos] using hd x hx

theorem moore_dirichlet_uniqueness {n : ℕ} (hn : 1 ≤ n)
    {A C : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f g : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hAC : ∀ x ∈ interior K, A x * C x = 1)
    (hCA : ∀ x ∈ interior K, C x * A x = 1)
    (hdet : ∀ x ∈ interior K, 0 < OAI.LinearAlgebra.Moore.mooreDet n (A x))
    (hL : ∀ x ∈ interior K, mooreLinearization A f x = mooreLinearization A g x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x = g x) : EqOn f g K := by
  have hfg := moore_dirichlet_comparison hn hK hf hg hA hAC hCA hdet
    (fun x hx ↦ (hL x hx).ge) (fun x hx hxi ↦ (hbd x hx hxi).le)
  have hgf := moore_dirichlet_comparison hn hK hg hf hA hAC hCA hdet
    (fun x hx ↦ (hL x hx).le) (fun x hx hxi ↦ (hbd x hx hxi).ge)
  exact fun x hx ↦ le_antisymm (hfg x hx) (hgf x hx)

end OAI.Analysis.PDE.Dirichlet
