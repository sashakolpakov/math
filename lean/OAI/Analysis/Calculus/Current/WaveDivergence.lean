import OAI.Analysis.Calculus.Current.Phase

/-! The paired divergence equations for the actual oscillatory current fields. -/

namespace OAI.Analysis.Calculus.Current

noncomputable section

def realD {d : ℕ} (f : (Index d → ℝ) → ℂ) (x : Index d → ℝ) (a : Index d) : ℂ :=
  deriv (fun t : ℝ => f (realLine x a t)) 0

def wavePairedC {d : ℕ} (κ κ' cR cI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (a b : Index d) : ℂ :=
  pairedC κ κ' v v' z a b * (phaseF cR cI (phaseDifference κ κ' v v') x : ℂ)

def wavePairedE {d : ℕ} (κ κ' cR cI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (a b : Index d) : ℂ :=
  pairedE κ κ' v v' z a b * (phaseG cR cI (phaseDifference κ κ' v v') x : ℂ)

theorem realD_wavePairedC {d : ℕ} (κ κ' cR cI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (a b : Index d) :
    realD (fun q => wavePairedC κ κ' cR cI v v' q z a b) x a =
      pairedC κ κ' v v' z a b * (-(phaseDifference κ κ' v v' a : ℂ) *
        (phaseG cR cI (phaseDifference κ κ' v v') x : ℂ)) := by
  have hh := (hasDerivAt_phaseF_line cR cI (phaseDifference κ κ' v v') x a).ofReal_comp.const_mul
    (pairedC κ κ' v v' z a b)
  simpa only [realD, wavePairedC, Complex.ofReal_mul, Complex.ofReal_neg] using hh.deriv

theorem realD_wavePairedE {d : ℕ} (κ κ' cR cI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (a b : Index d) :
    realD (fun q => wavePairedE κ κ' cR cI v v' q z a b) x a =
      pairedE κ κ' v v' z a b * ((phaseDifference κ κ' v v' a : ℂ) *
        (phaseF cR cI (phaseDifference κ κ' v v') x : ℂ)) := by
  have hh := (hasDerivAt_phaseG_line cR cI (phaseDifference κ κ' v v') x a).ofReal_comp.const_mul
    (pairedE κ κ' v v' z a b)
  simpa only [realD, wavePairedE, Complex.ofReal_mul] using hh.deriv

theorem barD_star_mul_real {d : ℕ} (f : (Index d → ℂ) → ℂ) (c : ℝ)
    (z : Index d → ℂ) (hf : DifferentiableAt ℝ f z) (a : Index d) :
    barD (fun w => star (f w * (c : ℂ))) z a =
      barD (fun w => star (f w)) z a * (c : ℂ) := by
  have heq : (fun w => star (f w * (c : ℂ))) = (fun w => star (f w) * (c : ℂ)) := by
    funext w
    simp [star_mul, mul_comm]
  rw [heq, barD_mul_const _ _ z hf.star]

theorem barD_wavePairedC {d : ℕ} (κ κ' cR cI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) (a b : Index d) :
    barD (fun w => star (wavePairedC κ κ' cR cI v v' x w a b)) z a =
      barD (fun w => star (pairedC κ κ' v v' w a b)) z a *
        (phaseF cR cI (phaseDifference κ κ' v v') x : ℂ) :=
  barD_star_mul_real _ _ z (differentiableAt_pairedC κ κ' v v' z hY a b) a

theorem barD_wavePairedE {d : ℕ} (κ κ' cR cI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) (a b : Index d) :
    barD (fun w => star (wavePairedE κ κ' cR cI v v' x w a b)) z a =
      barD (fun w => star (pairedE κ κ' v v' w a b)) z a *
        (phaseG cR cI (phaseDifference κ κ' v v') x : ℂ) :=
  barD_star_mul_real _ _ z (differentiableAt_pairedE κ κ' v v' z hY a b) a

/-- First equation in (paired-divergence), with the actual sine/cosine phase
and Gaussian fields and their actual coordinate derivatives. -/
theorem wavePaired_divergence_first {d : ℕ} (κ κ' cR cI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    (∑ a : Index d, (realD (fun q => wavePairedC κ κ' cR cI v v' q z a b) x a +
      barD (fun w => star (wavePairedE κ κ' cR cI v v' x w a b)) z a)) = 0 := by
  have hc : (∑ a, (phaseDifference κ κ' v v' a : ℂ) * pairedC κ κ' v v' z a b) =
      ∑ a, barD (fun w => star (pairedE κ κ' v v' w a b)) z a := by
    rw [phase_contraction_pairedC, pairedE_imaginary_divergence κ κ' v v' z hY]
  simp_rw [realD_wavePairedC, barD_wavePairedE κ κ' cR cI v v' x z hY]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hs : (∑ a, pairedC κ κ' v v' z a b *
        (-(phaseDifference κ κ' v v' a : ℂ) *
          (phaseG cR cI (phaseDifference κ κ' v v') x : ℂ))) =
      -(∑ a, (phaseDifference κ κ' v v' a : ℂ) * pairedC κ κ' v v' z a b) *
        (phaseG cR cI (phaseDifference κ κ' v v') x : ℂ) := by
    calc
      _ = ∑ a, -((phaseDifference κ κ' v v' a : ℂ) * pairedC κ κ' v v' z a b) *
          (phaseG cR cI (phaseDifference κ κ' v v') x : ℂ) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  rw [hs, hc]
  ring

/-- Second equation in (paired-divergence). No differential identity is assumed. -/
theorem wavePaired_divergence_second {d : ℕ} (κ κ' cR cI : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    (∑ a : Index d, (realD (fun q => wavePairedE κ κ' cR cI v v' q z a b) x a -
      barD (fun w => star (wavePairedC κ κ' cR cI v v' x w a b)) z a)) = 0 := by
  have hc : (∑ a, (phaseDifference κ κ' v v' a : ℂ) * pairedE κ κ' v v' z a b) =
      ∑ a, barD (fun w => star (pairedC κ κ' v v' w a b)) z a := by
    rw [phase_contraction_pairedE, pairedC_imaginary_divergence κ κ' v v' z hY]
  simp_rw [realD_wavePairedE, barD_wavePairedC κ κ' cR cI v v' x z hY]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hs : (∑ a, pairedE κ κ' v v' z a b *
        ((phaseDifference κ κ' v v' a : ℂ) *
          (phaseF cR cI (phaseDifference κ κ' v v') x : ℂ))) =
      (∑ a, (phaseDifference κ κ' v v' a : ℂ) * pairedE κ κ' v v' z a b) *
        (phaseF cR cI (phaseDifference κ κ' v v') x : ℂ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hs, hc]
  ring

end
end OAI.Analysis.Calculus.Current
