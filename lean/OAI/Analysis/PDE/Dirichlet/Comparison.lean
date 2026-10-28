import OAI.Analysis.PDE.Dirichlet.Linearized
import OAI.LinearAlgebra.Moore.Monotone

open Filter Set
open scoped Topology Matrix ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- The quadratic perturbation makes the Hessian gap strictly positive at a
local maximum of the difference. This is an actual second-derivative statement. -/
theorem quaternionHessian_gap_posDef {n : ℕ}
    {f g : CoordinateSpace n 4 → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    {ε : ℝ} (hε : 0 < ε) {x : CoordinateSpace n 4}
    (hmax : IsLocalMax (fun y ↦ (f y + (-1 : ℝ) • g y) + ε • ‖y‖ ^ 2) x) :
    (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x - quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef := by
  let F : CoordinateSpace n 4 → ℝ := fun y ↦ (f y + (-1 : ℝ) • g y) + ε • ‖y‖ ^ 2
  have hb : ContDiff ℝ 2 (fun y : CoordinateSpace n 4 ↦ ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  have hF : ContDiff ℝ 2 F := (hf.add (hg.const_smul (-1 : ℝ))).add (hb.const_smul ε)
  have hN := OAI.LinearAlgebra.Moore.complexify_hessianMap_posSemidef OAI.Analysis.Calculus.Quaternion.fourSlots
    (realHessian_neg_posSemidef_of_localMax hF hmax)
  have hn : OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (-realHessian F x) = -quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots F x := by
    rw [← neg_one_smul ℝ (realHessian F x), OAI.Analysis.Calculus.Quaternion.hessianMap_smul]
    simp only [quaternionHessian, neg_one_smul]
  rw [hn] at hN
  have hHF : quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots F x =
      quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x + (-1 : ℝ) • quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x +
        (8 * ε) • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) := by
    dsimp only [F]
    rw [quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots (hf.add (hg.const_smul (-1 : ℝ))) hb,
      quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hf hg, quaternionHessian_four_norm_sq, smul_smul]
    congr 1
    congr 1
    ring
  have hgap : quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x - quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x =
      -quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots F x +
        (8 * ε) • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) := by
    rw [hHF]
    module
  rw [hgap, OAI.LinearAlgebra.Moore.complexify_add, OAI.LinearAlgebra.Moore.complexify_real_smul, OAI.LinearAlgebra.Moore.complexify_one]
  exact Matrix.PosDef.posSemidef_add hN (Matrix.PosDef.one.smul (by positivity : 0 < 8 * ε))

/-- Nonlinear comparison for the quaternionic Monge–Ampère equation. All
Hessians and determinants are the actual differential/algebraic operators. -/
theorem quaternionic_dirichlet_comparison {n : ℕ} (hn : 1 ≤ n)
    {f g : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfpos : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef)
    (hdet : ∀ x ∈ interior K,
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x) ≤ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x))
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ g x) : ∀ x ∈ K, f x ≤ g x := by
  intro x hx
  let b : CoordinateSpace n 4 → ℝ := fun y ↦ ‖y‖ ^ 2
  have hb : ContDiff ℝ 2 b := contDiff_norm_sq ℝ
  obtain ⟨z, hz, hbmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hb.continuous.continuousOn
  have hε (ε : ℝ) (hε : 0 < ε) : f x - g x + ε * b x ≤ ε * b z := by
    let F : CoordinateSpace n 4 → ℝ := fun y ↦ (f y + (-1 : ℝ) • g y) + ε • b y
    have hF : ContDiff ℝ 2 F := (hf.add (hg.const_smul (-1 : ℝ))).add (hb.const_smul ε)
    obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hF.continuous.continuousOn
    by_cases hyi : y ∈ interior K
    · have hlocal := hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hyi)
      have hgap := quaternionHessian_gap_posDef hf hg hε hlocal
      have hne : quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y ≠ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f y := by
        intro heq
        have hd := hgap.diag_pos (i := ((⟨0, by omega⟩ : Fin n), (0 : Fin 2)))
        have hr := (Complex.pos_iff.mp hd).1
        simp [heq, OAI.LinearAlgebra.Moore.complexify, OAI.LinearAlgebra.Moore.quaternionMatrix] at hr
      have hlt := OAI.LinearAlgebra.Moore.mooreDet_lt_of_posSemidef_difference
        (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f y) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)
        (hfpos y hyi) hgap.posSemidef hne
      exact False.elim (not_lt_of_ge (hdet y hyi) hlt)
    · have hxy := hmax hx
      have hboundary := hbd y hy hyi
      have hbb := mul_le_mul_of_nonneg_left (hbmax hy) hε.le
      change f x + (-1 : ℝ) * g x + ε * b x ≤ f y + (-1 : ℝ) * g y + ε * b y at hxy
      linarith
  have ht : Tendsto (fun ε : ℝ ↦ f x - g x + ε * b x - ε * b z)
      (𝓝[>] 0) (𝓝 (f x - g x)) := by
    have hc : Continuous (fun ε : ℝ ↦ f x - g x + ε * b x - ε * b z) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ ε : ℝ in 𝓝[>] 0, f x - g x + ε * b x - ε * b z ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hpos
    exact sub_nonpos.mpr (hε ε hpos)
  have := le_of_tendsto ht hle
  linarith

theorem quaternionic_dirichlet_uniqueness {n : ℕ} (hn : 1 ≤ n)
    {f g : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfpos : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef)
    (hgpos : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x)).PosDef)
    (hdet : ∀ x ∈ interior K,
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x) = OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x))
    (hbd : ∀ x ∈ K, x ∉ interior K → f x = g x) : EqOn f g K := by
  have hfg := quaternionic_dirichlet_comparison hn hK hf hg hfpos
    (fun x hx ↦ (hdet x hx).ge) (fun x hx hxi ↦ (hbd x hx hxi).le)
  have hgf := quaternionic_dirichlet_comparison hn hK hg hf hgpos
    (fun x hx ↦ (hdet x hx).le) (fun x hx hxi ↦ (hbd x hx hxi).ge)
  exact fun x hx ↦ le_antisymm (hfg x hx) (hgf x hx)

end OAI.Analysis.PDE.Dirichlet
