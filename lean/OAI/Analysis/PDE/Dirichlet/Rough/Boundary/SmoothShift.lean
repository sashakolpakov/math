import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.Shift
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ParametricInverse

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A bounded family of linear perturbations of the identity is uniformly
invertible for small scalar parameters. -/
theorem exists_uniform_small_linear_perturbation (M : ℝ) (hM : 0 ≤ M) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t| < d → ∀ B : E →L[ℝ] E,
      ‖B‖ ≤ M → (ContinuousLinearMap.id ℝ E + t • B).IsInvertible := by
  have hi : (ContinuousLinearMap.id ℝ E).IsInvertible :=
    ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hi.eventually_nhds
  refine ⟨ε / (M + 1), div_pos hε (by positivity), ?_⟩
  intro t ht B hB
  apply hball
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  calc
    |t| * ‖B‖ ≤ |t| * M := mul_le_mul_of_nonneg_left hB (abs_nonneg t)
    _ ≤ |t| * (M + 1) := by gcongr; linarith
    _ < ε := (lt_div_iff₀ (by positivity : 0 < M + 1)).mp ht

omit [CompleteSpace E] in
theorem fderiv_add_smul_id {g : E → E} (hg : Differentiable ℝ g) (t : ℝ) (x : E) :
    fderiv ℝ (fun y ↦ y + t • g y) x =
      ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x := by
  exact ((hasFDerivAt_id x).add ((hg x).hasFDerivAt.const_smul t)).fderiv

/-- A smooth Lipschitz displacement gives a genuinely smooth family of global
inverses near the identity. The inverse is the actual set-theoretic inverse. -/
theorem exists_smooth_small_displacement_inverse [Nontrivial E]
    {g : E → E} {K : NNReal} (hg : ContDiff ℝ ∞ g) (hK : LipschitzWith K g) :
    ∃ d : ℝ, 0 < d ∧
      (∀ t : ℝ, |t| < d → Function.Bijective (fun x ↦ x + t • g x)) ∧
      ContDiffOn ℝ ∞
        (fun p : ℝ × E ↦ Function.invFun (fun x ↦ x + p.1 • g x) p.2)
        {p | |p.1| < d} := by
  obtain ⟨d, hd, hderiv⟩ := exists_uniform_small_linear_perturbation (E := E) (K : ℝ) K.coe_nonneg
  let a : ℝ := min d ((K + 1 : ℝ)⁻¹)
  have ha : 0 < a := lt_min hd (inv_pos.mpr (by positivity))
  have hbij (t : ℝ) (ht : |t| < a) : Function.Bijective (fun x ↦ x + t • g x) := by
    have hc : ‖t‖₊ * K < 1 := by
      change |t| * (K : ℝ) < 1
      have hta : |t| < (K + 1 : ℝ)⁻¹ := lt_of_lt_of_le ht (min_le_right _ _)
      calc
        |t| * (K : ℝ) ≤ |t| * (K + 1 : ℝ) := by gcongr; linarith
        _ < 1 := (lt_div_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mp (by simpa only [one_div] using hta)
    have hl : LipschitzWith (‖t‖₊ * K) (fun x ↦ t • g x) := by
      rw [lipschitzWith_iff_norm_sub_le]
      intro x y
      rw [← smul_sub, norm_smul]
      change ‖t‖ * ‖g x - g y‖ ≤ (‖t‖ * (K : ℝ)) * ‖x-y‖
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hK.norm_sub_le x y) (norm_nonneg t)
    obtain ⟨H, hH⟩ := exists_homeomorph_of_lipschitz_displacement
      (fun x ↦ t • g x) hl hc
    have heq : (fun x ↦ x + t • g x) = H := funext (fun x ↦ (hH x).symm)
    rw [heq]
    exact H.bijective
  refine ⟨a, ha, hbij, ?_⟩
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_parametric_invFun (fun p : ℝ × E ↦ p.2 + p.1 • g p.2) (by simp)
  · have hopen : IsOpen {t : ℝ | |t| < a} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds hp] with t ht
    exact hbij t ht
  · exact (contDiff_snd.add (contDiff_fst.smul (hg.comp contDiff_snd))).contDiffAt
  · rw [fderiv_add_smul_id (hg.differentiable (by simp))]
    exact hderiv p.1 (lt_of_lt_of_le hp (min_le_left _ _)) _
      (norm_fderiv_le_of_lipschitz ℝ hK)

theorem exists_smooth_cutoffShift_inverse [Nontrivial E]
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (v : E) :
    ∃ d : ℝ, 0 < d ∧
      (∀ t : ℝ, |t| < d → Function.Bijective (cutoffShift η v t)) ∧
      ContDiffOn ℝ ∞
        (fun p : ℝ × E ↦ Function.invFun (cutoffShift η v p.1) p.2)
        {p | |p.1| < d} := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hη (by simp)
  have hl : LipschitzWith (K * ‖v‖₊) (fun x ↦ η x • v) := by
    simpa using cutoffShift_displacement_lipschitz hK v 1
  have he (t : ℝ) : cutoffShift η v t = fun x ↦ x + t • (η x • v) := by
    funext x
    simp only [cutoffShift, mul_smul]
  simp_rw [he]
  exact exists_smooth_small_displacement_inverse (g := fun x ↦ η x • v)
    (hη.smul contDiff_const) hl

end OAI.Analysis.PDE.Dirichlet
