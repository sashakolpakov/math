import OAI.Analysis.ODE.SmoothFlow.Local
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace OAI.Analysis.ODE.SmoothFlow

section Directional
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_directional_at {Φ : X→E} {p : X}
    (hΦ : ContDiffAt ℝ 2 Φ p) (v w : X) :
    fderiv ℝ (fun y => fderiv ℝ Φ y v) p w = fderiv ℝ (fderiv ℝ Φ) p w v := by
  have hd := ((hΦ.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have ha := hd.clm_apply (hasFDerivAt_const v p)
  rw [ha.fderiv]
  simp

/-- Differentiation of a directional first-order equation, using actual symmetry
of the second derivative to interchange the two directions. -/
theorem directional_equation_variation {Φ : X→E} {f : E→E} {p : X}
    (hΦ : ContDiffAt ℝ 2 Φ p) (hf : DifferentiableAt ℝ f (Φ p))
    (v w : X) (heq : (fun y => fderiv ℝ Φ y v) =ᶠ[𝓝 p] (fun y => f (Φ y))) :
    fderiv ℝ (fderiv ℝ Φ) p v w = fderiv ℝ f (Φ p) (fderiv ℝ Φ p w) := by
  calc
    fderiv ℝ (fderiv ℝ Φ) p v w = fderiv ℝ (fderiv ℝ Φ) p w v :=
      hΦ.isSymmSndFDerivAt (by norm_num) v w
    _ = fderiv ℝ (fun y => fderiv ℝ Φ y v) p w := (fderiv_directional_at hΦ v w).symm
    _ = fderiv ℝ (fun y => f (Φ y)) p w := by rw [heq.fderiv_eq]
    _ = fderiv ℝ f (Φ p) (fderiv ℝ Φ p w) := by
      change fderiv ℝ (f ∘ Φ) p w = _
      rw [(hf.hasFDerivAt.comp p (hΦ.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
      rfl

end Directional

variable {Z E : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_time_hasDerivAt {Φ : Z×ℝ→E} {z : Z} {t : ℝ}
    (hΦ : DifferentiableAt ℝ Φ (z,t)) :
    HasDerivAt (fun s => Φ (z,s)) (fderiv ℝ Φ (z,t) (0,1)) t := by
  have hl : HasDerivAt (fun s : ℝ => (z,s)) ((0:Z),(1:ℝ)) t := by
    simpa using (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  exact hΦ.hasFDerivAt.comp_hasDerivAt t hl

theorem joint_parameter_fderiv {Φ : Z×ℝ→E} {z : Z} {t : ℝ}
    (hΦ : DifferentiableAt ℝ Φ (z,t)) (w : Z) :
    fderiv ℝ (fun y => Φ (y,t)) z w = fderiv ℝ Φ (z,t) (w,0) := by
  have hl : HasFDerivAt (fun y : Z => (y,t)) (ContinuousLinearMap.inl ℝ Z ℝ) z := by
    convert! (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z) using 1
  change fderiv ℝ (Φ ∘ (fun y : Z => (y,t))) z w = _
  rw [(hΦ.hasFDerivAt.comp z hl).fderiv]
  rfl

/-- The parameter derivative of a jointly smooth family of genuine ODE
solutions solves the actual linear variational equation. -/
theorem flow_parameter_variation {V : Set Z} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) {Φ : Z×ℝ→E} {f : E→E}
    (hΦ : ContDiffOn ℝ 2 Φ (V×ˢI))
    (hf : ∀z∈V, ∀t∈I, DifferentiableAt ℝ f (Φ (z,t)))
    (hode : ∀z∈V, ∀t∈I, HasDerivAt (fun s => Φ (z,s)) (f (Φ (z,t))) t)
    {z : Z} (hz : z∈V) (w : Z) {t : ℝ} (ht : t∈I) :
    HasDerivAt (fun s => fderiv ℝ (fun y => Φ (y,s)) z w)
      (fderiv ℝ f (Φ (z,t)) (fderiv ℝ (fun y => Φ (y,t)) z w)) t := by
  have hloc (y : Z) (hy : y∈V) (s : ℝ) (hs : s∈I) : ContDiffAt ℝ 2 Φ (y,s) :=
    (hΦ (y,s) ⟨hy,hs⟩).contDiffAt ((hV.prod hI).mem_nhds ⟨hy,hs⟩)
  have heq : (fun p : Z×ℝ => fderiv ℝ Φ p (0,1)) =ᶠ[𝓝 (z,t)] (fun p => f (Φ p)) := by
    filter_upwards [(hV.prod hI).mem_nhds (show (z,t)∈V×ˢI from ⟨hz,ht⟩)] with p hp
    exact (joint_time_hasDerivAt ((hloc p.1 hp.1 p.2 hp.2).differentiableAt
      (by norm_num))).unique (hode p.1 hp.1 p.2 hp.2)
  have hswap := directional_equation_variation (hloc z hz t ht) (hf z hz t ht)
    ((0:Z),(1:ℝ)) (w,0) heq
  have hd := (((hloc z hz t ht).fderiv_right (m:=1) (by norm_num)).differentiableAt
    one_ne_zero).hasFDerivAt
  have ha := hd.clm_apply (hasFDerivAt_const (w,(0:ℝ)) (z,t))
  have hl : HasDerivAt (fun s : ℝ => (z,s)) ((0:Z),(1:ℝ)) t := by
    simpa using (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  have hj := ha.comp_hasDerivAt t hl
  have hj' : HasDerivAt (fun s => fderiv ℝ Φ (z,s) (w,0))
      (fderiv ℝ (fderiv ℝ Φ) (z,t) (0,1) (w,0)) t := by
    simpa [Function.comp_def] using hj
  rw [hswap, ←joint_parameter_fderiv ((hloc z hz t ht).differentiableAt (by norm_num)) w] at hj'
  apply hj'.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds ht] with s hs
  exact joint_parameter_fderiv ((hloc z hz s hs).differentiableAt (by norm_num)) w

/-- Parameter differentiation of any prescribed initial condition. -/
theorem flow_parameter_initial_eq {V : Set Z} (hV : IsOpen V)
    {Φ : Z×ℝ→E} {g : Z→E} (hinitial : ∀z∈V, Φ (z,0)=g z)
    {z : Z} (hz : z∈V) :
    fderiv ℝ (fun y => Φ (y,0)) z = fderiv ℝ g z := by
  have he : (fun y => Φ (y,0)) =ᶠ[𝓝 z] g := by
    filter_upwards [hV.mem_nhds hz] with y hy
    exact hinitial y hy
  exact he.fderiv_eq

/-- Initial-point differentiation of the genuine identity initial condition. -/
theorem flow_parameter_initial {V : Set E} (hV : IsOpen V) {Φ : E×ℝ→E}
    (hinitial : ∀z∈V, Φ (z,0)=z) {z : E} (hz : z∈V) (w : E) :
    fderiv ℝ (fun y => Φ (y,0)) z w = w := by
  have he : (fun y => Φ (y,0)) =ᶠ[𝓝 z] id := by
    filter_upwards [hV.mem_nhds hz] with y hy
    exact hinitial y hy
  rw [he.fderiv_eq]
  simp

end OAI.Analysis.ODE.SmoothFlow
