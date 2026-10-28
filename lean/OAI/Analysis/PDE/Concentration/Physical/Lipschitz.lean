import OAI.Analysis.PDE.Concentration.CompactLipschitz
import OAI.Analysis.PDE.Concentration.PatchVolume
import OAI.Analysis.PDE.Green.Physical.JointExtension

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Green
open scoped ContDiff

def normalizedPhysicalFiber (d : ℕ) : Set (ℂ × (Option (Fin d) → ℂ)) :=
  (fun p : ℂ × (Option (Fin d) → ℂ) => (p.1, OAI.Analysis.Calculus.Current.physicalFiberInverse 1 p.1 p.2)) ''
    OAI.Analysis.Calculus.Current.normalizedInverseParameters d

theorem isCompact_normalizedPhysicalFiber (d : ℕ) : IsCompact (normalizedPhysicalFiber d) := by
  apply (OAI.Analysis.Calculus.Current.isCompact_normalizedInverseParameters d).image_of_continuousOn
  intro p hp
  exact (continuousAt_fst.prodMk
    (((OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse_joint 1 p.1 p.2
      (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hp.2)).restrict_scalars ℝ).continuousAt)).continuousWithinAt

theorem normalizedPhysicalFiber_subset (d : ℕ) :
    normalizedPhysicalFiber d ⊆ OAI.Analysis.PDE.Green.physicalJointRegularDomain d := by
  rintro p ⟨q, hq, rfl⟩
  change OAI.Analysis.Calculus.Current.physicalEmbedding q.1 (OAI.Analysis.Calculus.Current.physicalFiberInverse 1 q.1 q.2) none ≠ 0
  rw [OAI.Analysis.Calculus.Current.physicalEmbedding_inverse]
  exact OAI.Analysis.Calculus.Current.fiberInverse_Y_ne_zero _ _ _
    (OAI.Analysis.Calculus.Current.fiberParameterBall_numerator 1 q.1 (by norm_num) hq.1.1 hq.2)
    (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hq.2)

theorem contDiffOn_physicalCoordinates_joint (d : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℂ × (Option (Fin d) → ℂ) => OAI.Analysis.Calculus.Current.physicalFiberCoordinates 1 p.1 p.2)
      (OAI.Analysis.PDE.Green.physicalJointRegularDomain d) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  cases i with
  | none =>
    simpa only [OAI.Analysis.Calculus.Current.physicalFiberCoordinates, Complex.ofReal_one, div_one, Function.comp_def] using
      ((OAI.Analysis.Calculus.Current.contDiffAt_phi_real _ hp).of_le (by simp)).comp p (OAI.Analysis.PDE.Green.contDiff_physicalEmbedding_joint d ∞).contDiffAt
  | some i =>
    exact ((OAI.Analysis.Calculus.Current.contDiffAt_ratio _ hp i).of_le (by simp)).comp p (OAI.Analysis.PDE.Green.contDiff_physicalEmbedding_joint d ∞).contDiffAt

/-- Uniform short-displacement control for the genuine normalized physical
coordinate map. It is proved on the entire compact family of physical
fibers, before the output patch or semiclassical scale is chosen. -/
theorem normalized_physical_coordinates_lipschitz (d : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (τ : ℂ) (u q : Option (Fin d) → ℂ),
      1 ≤ ‖τ‖ → ‖τ‖ ≤ 4 → u ∈ OAI.Analysis.Calculus.Current.fiberParameterBall d →
      ‖q - OAI.Analysis.Calculus.Current.physicalFiberInverse 1 τ u‖ ≤ δ →
      OAI.Analysis.Calculus.Current.physicalEmbedding τ q none ≠ 0 ∧
        ‖OAI.Analysis.Calculus.Current.physicalFiberCoordinates 1 τ q - u‖ ≤ C * ‖q - OAI.Analysis.Calculus.Current.physicalFiberInverse 1 τ u‖ := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := compact_uniform_local_lipschitz
    (isCompact_normalizedPhysicalFiber d) (OAI.Analysis.PDE.Green.isOpen_physicalJointRegularDomain d)
    (normalizedPhysicalFiber_subset d) (contDiffOn_physicalCoordinates_joint d)
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro τ u q ht ht' hu hq
  have he : ‖(τ, q) - (τ, OAI.Analysis.Calculus.Current.physicalFiberInverse 1 τ u)‖ = ‖q - OAI.Analysis.Calculus.Current.physicalFiberInverse 1 τ u‖ := by
    simp only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  have hpair : (τ, OAI.Analysis.Calculus.Current.physicalFiberInverse 1 τ u) ∈ normalizedPhysicalFiber d :=
    ⟨(τ, u), ⟨⟨ht, ht'⟩, hu⟩, rfl⟩
  have hh := hb _ hpair (τ, q) (he.symm ▸ hq)
  dsimp only at hh
  rw [OAI.Analysis.Calculus.Current.physicalCoordinates_right_inverse 1 τ u (by norm_num)
    (OAI.Analysis.Calculus.Current.fiberParameterBall_numerator 1 τ (by norm_num) ht hu) (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hu), he] at hh
  exact hh

theorem physicalEmbedding_smul {d : ℕ} (a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ) :
    OAI.Analysis.Calculus.Current.physicalEmbedding (a • τ) (a • q) = a • OAI.Analysis.Calculus.Current.physicalEmbedding τ q := by
  have he : OAI.Analysis.Calculus.Current.physicalTimeOffset (d := d) (a • τ) = a • OAI.Analysis.Calculus.Current.physicalTimeOffset τ := by
    ext i
    cases i with
    | none => simp [OAI.Analysis.Calculus.Current.physicalTimeOffset]; ring
    | some i => cases i <;> simp [OAI.Analysis.Calculus.Current.physicalTimeOffset] ; ring
  simp only [OAI.Analysis.Calculus.Current.physicalEmbedding, map_smul, he, smul_add]

theorem physicalFiberCoordinates_smul {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (τ : ℂ) (q : Option (Fin d) → ℂ) :
    OAI.Analysis.Calculus.Current.physicalFiberCoordinates a (a • τ) (a • q) = OAI.Analysis.Calculus.Current.physicalFiberCoordinates 1 τ q := by
  ext i
  cases i with
  | none =>
    change OAI.Analysis.Calculus.Current.phi (OAI.Analysis.Calculus.Current.physicalEmbedding (a • τ) (a • q)) / (a : ℂ) = OAI.Analysis.Calculus.Current.phi (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) / 1
    rw [physicalEmbedding_smul, OAI.Analysis.Calculus.Current.phi_smul_real a ha]
    simp only [Complex.real_smul, div_one]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast ha : (a : ℂ) ≠ 0)
  | some i =>
    simp only [OAI.Analysis.Calculus.Current.physicalFiberCoordinates, physicalEmbedding_smul, OAI.Analysis.Calculus.Current.ratio_smul_real a ha]

/-- The forward physical coordinate map varies by at most `C/a` on one
uniform neighborhood of every physical fiber with `a≤|τ|≤4a`. -/
theorem physical_coordinates_lipschitz (d : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (a : ℝ) (τ : ℂ) (u q : Option (Fin d) → ℂ),
      0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 * a → u ∈ OAI.Analysis.Calculus.Current.fiberParameterBall d →
      ‖q - OAI.Analysis.Calculus.Current.physicalFiberInverse a τ u‖ ≤ a * δ →
      OAI.Analysis.Calculus.Current.physicalEmbedding τ q none ≠ 0 ∧
        ‖OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ q - u‖ ≤ (C / a) * ‖q - OAI.Analysis.Calculus.Current.physicalFiberInverse a τ u‖ := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := normalized_physical_coordinates_lipschitz d
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro a τ u q ha ht ht' hu hq
  have hτ : ‖a⁻¹ • τ‖ = ‖τ‖ / a := by
    simp [Real.norm_eq_abs, abs_of_pos ha, div_eq_mul_inv, mul_comm]
  have ht1 : 1 ≤ ‖a⁻¹ • τ‖ := by rw [hτ]; exact (le_div_iff₀ ha).mpr (by simpa using ht)
  have ht4 : ‖a⁻¹ • τ‖ ≤ 4 := by rw [hτ]; exact (div_le_iff₀ ha).mpr (by nlinarith)
  have hq0 := OAI.Analysis.Calculus.Current.physicalFiberInverse_scale a (a⁻¹ • τ) u
  rw [smul_inv_smul₀ ha.ne'] at hq0
  have he : ‖a⁻¹ • q - OAI.Analysis.Calculus.Current.physicalFiberInverse 1 (a⁻¹ • τ) u‖ =
      ‖q - OAI.Analysis.Calculus.Current.physicalFiberInverse a τ u‖ / a := by
    have hv : a⁻¹ • q - OAI.Analysis.Calculus.Current.physicalFiberInverse 1 (a⁻¹ • τ) u =
        a⁻¹ • (q - OAI.Analysis.Calculus.Current.physicalFiberInverse a τ u) := by
      rw [hq0, smul_sub, inv_smul_smul₀ ha.ne']
    rw [hv]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos ha, div_eq_mul_inv, mul_comm]
  have hin : ‖a⁻¹ • q - OAI.Analysis.Calculus.Current.physicalFiberInverse 1 (a⁻¹ • τ) u‖ ≤ δ := by
    rw [he]
    exact (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using hq)
  have hh := hb (a⁻¹ • τ) u (a⁻¹ • q) ht1 ht4 hu hin
  have hcoords := physicalFiberCoordinates_smul a ha.ne' (a⁻¹ • τ) (a⁻¹ • q)
  rw [smul_inv_smul₀ ha.ne', smul_inv_smul₀ ha.ne'] at hcoords
  have hemp := physicalEmbedding_smul a (a⁻¹ • τ) (a⁻¹ • q)
  rw [smul_inv_smul₀ ha.ne', smul_inv_smul₀ ha.ne'] at hemp
  constructor
  · rw [hemp, Pi.smul_apply]
    exact smul_ne_zero ha.ne' hh.1
  · rw [← hcoords, he] at hh
    convert hh.2 using 1 ; ring

end OAI.Analysis.PDE.Concentration
