import OAI.Analysis.Fourier.WavePackets.AngularGrid
import OAI.Analysis.Fourier.WavePackets.UniformSectorKernel

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter
open scoped ContDiff Topology ENNReal FourierTransform

def angularChartRescale {d : ℕ} (γ : ℝ) (c : Fin d → ℝ)
    (ξ : Space (d + 1)) : Space (d + 1) :=
  WithLp.toLp 2 (Fin.cases (ξ 0) (fun i => γ * ξ i.succ + c i * ξ 0))

@[simp] theorem angularChartRescale_zero {d : ℕ} (γ : ℝ) (c : Fin d → ℝ)
    (ξ : Space (d + 1)) : angularChartRescale γ c ξ 0 = ξ 0 := rfl

@[simp] theorem angularChartRescale_succ {d : ℕ} (γ : ℝ) (c : Fin d → ℝ)
    (ξ : Space (d + 1)) (i : Fin d) :
    angularChartRescale γ c ξ i.succ = γ * ξ i.succ + c i * ξ 0 := by
  simp [angularChartRescale]

theorem contDiff_angularChartRescale (d : ℕ) :
    ContDiff ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d + 1) =>
      angularChartRescale q.1.1 q.1.2 q.2) := by
  have heval (j : Fin (d + 1)) : ContDiff ℝ ∞ (fun ξ : Space (d + 1) => ξ j) := by
    fun_prop
  apply (contDiff_piLp 2).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [angularChartRescale_zero, Function.comp_def] using
      ((heval 0).comp contDiff_snd :
        ContDiff ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d + 1) => q.2 0))
  · simp only [angularChartRescale_succ]
    exact (contDiff_fst.fst.mul ((heval j.succ).comp contDiff_snd)).add
      (((contDiff_apply ℝ ℝ j).comp contDiff_fst.snd).mul
        ((heval 0).comp contDiff_snd))

def angularChartLinearEquiv {d : ℕ} (γ : ℝ) (hγ : γ ≠ 0) (c : Fin d → ℝ) :
    Space (d + 1) ≃L[ℝ] Space (d + 1) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := angularChartRescale γ c
    invFun := angularChartRescale γ⁻¹ (fun i => -γ⁻¹ * c i)
    map_add' := by
      intro x y
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [angularChartRescale_succ, PiLp.add_apply]
        ring
    map_smul' := by
      intro r x
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [angularChartRescale_succ, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
    left_inv := by
      intro x
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [angularChartRescale_succ, angularChartRescale_zero]
        field_simp
        ring
    right_inv := by
      intro x
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [angularChartRescale_succ, angularChartRescale_zero]
        field_simp
        ring }

def angularChartFamily {d : ℕ} (b : Space (d + 1) → ℂ)
    (q : (ℝ × (Fin d → ℝ)) × Space (d + 1)) : ℂ :=
  b (angularChartRescale q.1.1 q.1.2 q.2) *
    (angularGridProduct (fun i => q.2 i.succ / q.2 0) : ℂ)

def angularChartSymbol {d : ℕ} (b : Space (d + 1) → ℂ)
    (γ : ℝ) (c : Fin d → ℝ) (ξ : Space (d + 1)) : ℂ :=
  b ξ * (angularGridProduct (fun i => (ξ i.succ / ξ 0 - c i) / γ) : ℂ)

theorem contDiff_angularChartFamily {d : ℕ} {b : Space (d + 1) → ℂ}
    (hb : ContDiff ℝ ∞ b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) :
    ContDiff ℝ ∞ (angularChartFamily b) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q.2 0 = 0
  · have hnot : angularChartRescale q.1.1 q.1.2 q.2 ∉ tsupport b := by
      intro hm
      have := hs _ hm
      simp only [angularChartRescale_zero, hq] at this
      linarith
    apply (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : (ℝ × (Fin d → ℝ)) × Space (d + 1) => (0 : ℂ)) q).congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto
      (contDiff_angularChartRescale d).continuous.continuousAt] with p hp
    change b (angularChartRescale p.1.1 p.1.2 p.2) = 0 at hp
    simp only [angularChartFamily, hp, zero_mul]
  · apply (hb.comp (contDiff_angularChartRescale d)).contDiffAt.mul
    apply Complex.ofRealCLM.contDiff.contDiffAt.comp
    apply (contDiff_angularGridProduct d).contDiffAt.comp
    apply contDiffAt_pi.mpr
    intro i
    have hi : ContDiffAt ℝ ∞ (fun p : (ℝ × (Fin d → ℝ)) × Space (d + 1) =>
        p.2 i.succ) q := by fun_prop
    have h0 : ContDiffAt ℝ ∞ (fun p : (ℝ × (Fin d → ℝ)) × Space (d + 1) =>
        p.2 0) q := by fun_prop
    exact hi.div h0 hq

/-- All rescaled chart symbols have one common compact support, even
when the shear and scale parameters range over all real values. -/
theorem angularChartFamily_common_support {d : ℕ} {b : Space (d + 1) → ℂ}
    {B : ℝ} (hs : ∀ ξ ∈ tsupport b, ξ 0 ≠ 0 ∧ |ξ 0| ≤ B) :
    tsupport (angularChartFamily b) ⊆ Set.univ ×ˢ
      (WithLp.toLp 2 '' Set.Icc (fun _ : Fin (d + 1) => -B) (fun _ => B)) := by
  have hc : IsClosed (WithLp.toLp 2 ''
      Set.Icc (fun _ : Fin (d + 1) => -B) (fun _ => B)) :=
    (isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) => ℝ))).isClosed
  apply closure_minimal _ (isClosed_univ.prod hc)
  rintro ⟨q, ξ⟩ hξ
  have hb : b (angularChartRescale q.1 q.2 ξ) ≠ 0 := by
    intro hz
    exact hξ (by simp [angularChartFamily, hz])
  have hg : angularGridProduct (fun i => ξ i.succ / ξ 0) ≠ 0 := by
    intro hz
    exact hξ (by simp [angularChartFamily, hz])
  have hslab : ξ 0 ≠ 0 ∧ |ξ 0| ≤ B := by simpa using hs _ (subset_tsupport b hb)
  have h0 : |ξ 0| ≤ B := hslab.2
  refine ⟨Set.mem_univ _, ξ.ofLp, ?_, by simp⟩
  have hall (i : Fin (d + 1)) : |ξ i| ≤ B := by
    refine Fin.cases h0 (fun j => ?_) i
    have hratio := (angularGridProduct_ne_zero hg j).le
    rw [abs_div] at hratio
    have habs : 0 < |ξ 0| := abs_pos.mpr hslab.1
    exact ((div_le_iff₀ habs).mp hratio).trans (by simpa using h0)
  exact ⟨fun i => (abs_le.mp (hall i)).1, fun i => (abs_le.mp (hall i)).2⟩

theorem angularChartSymbol_eq_rescaled {d : ℕ} {b : Space (d + 1) → ℂ}
    (hb0 : ∀ ξ, ξ 0 = 0 → b ξ = 0) {γ : ℝ} (hγ : γ ≠ 0) (c : Fin d → ℝ) :
    angularChartSymbol b γ c = fun ξ =>
      angularChartFamily b ((γ, c), (angularChartLinearEquiv γ hγ c).symm ξ) := by
  funext ξ
  let A := angularChartLinearEquiv γ hγ c
  have hA : angularChartRescale γ c (A.symm ξ) = ξ := A.apply_symm_apply ξ
  change b ξ * _ = b (angularChartRescale γ c (A.symm ξ)) * _
  rw [hA]
  by_cases hξ : ξ 0 = 0
  · simp [hb0 ξ hξ]
  · congr 2
    congr 1
    funext i
    change (ξ i.succ / ξ 0 - c i) / γ =
      (γ⁻¹ * ξ i.succ + (-γ⁻¹ * c i) * ξ 0) / ξ 0
    field_simp
    ring

/-- Uniform inverse-kernel bounds for the actual translated projective
grid pieces. The centers need only stay in a fixed coordinate box. -/
theorem uniform_angularChartSymbol_kernel {d : ℕ} {b : Space (d + 1) → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
      ∀ c : Fin d → ℝ, (∀ i, |c i| ≤ R) →
      MeasureTheory.eLpNorm (𝓕⁻ (angularChartSymbol b γ c)) 1 MeasureTheory.volume ≤
        ENNReal.ofReal C := by
  obtain ⟨B, hB, hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hslab : ∀ ξ ∈ tsupport b, ξ 0 ≠ 0 ∧ |ξ 0| ≤ B := by
    intro ξ hξ
    refine ⟨ne_of_gt (ha.trans_le (hs ξ hξ)), ?_⟩
    have hcoord : |ξ 0| ≤ ‖ξ‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ 0
    exact hcoord.trans (hbound ξ hξ)
  let K : Set (ℝ × (Fin d → ℝ)) := Icc 0 1 ×ˢ Icc (fun _ => -R) (fun _ => R)
  let S : Set (Space (d + 1)) :=
    WithLp.toLp 2 '' Icc (fun _ : Fin (d + 1) => -B) (fun _ => B)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hS : IsCompact S := isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  obtain ⟨C, hC, hkernel⟩ := uniform_linearly_rescaled_inverse_kernel_bound hK hS
    (contDiff_angularChartFamily hb ha hs) (angularChartFamily_common_support hslab)
  refine ⟨C, hC, ?_⟩
  intro γ hγ hγ1 c hcR
  have hb0 : ∀ ξ, ξ 0 = 0 → b ξ = 0 := by
    intro ξ hξ
    by_contra hn
    have hh := hs ξ (subset_tsupport b hn)
    rw [hξ] at hh
    linarith
  rw [angularChartSymbol_eq_rescaled hb0 hγ.ne' c]
  apply hkernel (γ, c)
  exact ⟨⟨hγ.le, hγ1⟩, ⟨fun i => (abs_le.mp (hcR i)).1, fun i => (abs_le.mp (hcR i)).2⟩⟩

end OAI.Analysis.Fourier.WavePackets
