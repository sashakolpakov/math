import OAI.Analysis.PDE.Variational.ValueCutoff
import OAI.Analysis.PDE.Variational.LevelDerivative
import OAI.Analysis.PDE.Variational.L2Dominated
import OAI.Analysis.PDE.Weak.Elliptic.H1

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

def truncateValue (u : CellCoordinates m→ℝ) (c : ℝ) : CellCoordinates m→ℝ :=
  fun x ↦ valueCutoff c (u x)

theorem contDiff_truncateValue {u : CellCoordinates m→ℝ} (hu : ContDiff ℝ ∞ u) (c : ℝ) :
    ContDiff ℝ ∞ (truncateValue u c) := (contDiff_valueCutoff c).comp hu

theorem tsupport_truncateValue_subset (u : CellCoordinates m→ℝ) (c : ℝ) :
    tsupport (truncateValue u c)⊆tsupport u := by
  apply closure_mono
  intro x hx hzero
  exact hx (by simp only [truncateValue,hzero,valueCutoff_zero])

theorem hasCompactSupport_truncateValue {u : CellCoordinates m→ℝ}
    (hc : HasCompactSupport u) (c : ℝ) : HasCompactSupport (truncateValue u c) :=
  hc.of_isClosed_subset isClosed_closure (tsupport_truncateValue_subset u c)

theorem tsupport_truncateValue_inside {u : CellCoordinates m→ℝ} (hu : Continuous u)
    {Ω : Set (CellCoordinates m)} (hz : ∀x∉Ω,u x=0) (c : ℝ) :
    tsupport (truncateValue u c)⊆Ω := by
  have hsub : tsupport (truncateValue u c)⊆{x | 1≤|c*u x|} := by
    apply closure_minimal _ (isClosed_le continuous_const ((continuous_const.mul hu).abs))
    intro x hx
    exact (lt_of_not_ge (fun h ↦ hx (valueCutoff_eq_zero_of_small c (u x) h))).le
  intro x hx
  by_contra hxo
  have h := hsub hx
  change 1≤|c*u x| at h
  simp only [hz x hxo,mul_zero,abs_zero] at h
  linarith

theorem cellGradient_truncateValue {u : CellCoordinates m→ℝ} (hu : ContDiff ℝ 1 u)
    (c : ℝ) (x : CellCoordinates m) :
    cellGradient (truncateValue u c) x=valueCutoffSlope (c*u x) • cellGradient u x := by
  have h := (hasDerivAt_valueCutoff c (u x)).comp_hasFDerivAt x
    (hu.differentiable one_ne_zero x).hasFDerivAt
  change HasFDerivAt (truncateValue u c) (valueCutoffSlope (c*u x) • fderiv ℝ u x) x at h
  ext j
  change fderiv ℝ (truncateValue u c) x (Pi.single j 1)=_
  rw [h.fderiv]
  simp [cellGradient_apply]

theorem truncateValue_tendsto (u : CellCoordinates m→ℝ) (x : CellCoordinates m) :
    Tendsto (fun n:ℕ ↦ truncateValue u ((n:ℝ)+1) x) atTop (𝓝 (u x)) := by
  by_cases hx : u x=0
  · simpa only [truncateValue,hx,valueCutoff_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_large_nat_mul hx] with n hn
    exact (valueCutoff_eq_self_of_large _ _ hn.le).symm

theorem cellGradient_truncateValue_tendsto {u : CellCoordinates m→ℝ}
    (hu : ContDiff ℝ 1 u) :
    ∀ᵐ x ∂volume, Tendsto (fun n:ℕ ↦ cellGradient (truncateValue u ((n:ℝ)+1)) x)
      atTop (𝓝 (cellGradient u x)) := by
  filter_upwards [cellGradient_zero_ae_on_level hu] with x hx
  by_cases hzero : u x=0
  · simpa only [cellGradient_truncateValue hu,hx hzero,smul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:CellVectors m)) atTop (𝓝 0))
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_large_nat_mul hzero] with n hn
    rw [cellGradient_truncateValue hu,valueCutoffSlope_eq_one_of_large hn,one_smul]

/-- Smooth compact zero extensions are in the actual H¹ closure of smooth
functions compactly supported strictly inside the open domain. -/
theorem smooth_zero_extension_mem_H1Zero
    (u : CellCoordinates m→ℝ) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    {Ω : Set (CellCoordinates m)} (hz : ∀x∉Ω,u x=0) :
    OAI.Analysis.PDE.Weak.smoothH1Pair u hu hc∈OAI.Analysis.PDE.Weak.H1Zero Ω := by
  let v (n:ℕ) := truncateValue u ((n:ℝ)+1)
  have hv (n:ℕ) : ContDiff ℝ ∞ (v n) := contDiff_truncateValue hu _
  have hvc (n:ℕ) : HasCompactSupport (v n) := hasCompactSupport_truncateValue hc _
  have hm (n:ℕ) : OAI.Analysis.PDE.Weak.smoothH1Pair (v n) (hv n) (hvc n)∈OAI.Analysis.PDE.Weak.H1Zero Ω :=
    OAI.Analysis.PDE.Weak.smoothH1Pair_mem_H1Zero _ _ _ (tsupport_truncateValue_inside hu.continuous hz _)
  suffices hconv : Tendsto (fun n ↦ OAI.Analysis.PDE.Weak.smoothH1Pair (v n) (hv n) (hvc n)) atTop
      (𝓝 (OAI.Analysis.PDE.Weak.smoothH1Pair u hu hc)) from
    isClosed_closure.mem_of_tendsto hconv (Eventually.of_forall hm)
  apply Tendsto.prodMk_nhds
  · apply tendsto_toL2_of_dominated (fun n ↦ v n) u
      (fun n ↦ (hv n).continuous.memLp_of_hasCompactSupport (hvc n))
      (hu.continuous.memLp_of_hasCompactSupport hc) (fun x ↦ |u x|)
      (hu.continuous.memLp_of_hasCompactSupport hc).norm
    · exact fun n x ↦ abs_valueCutoff_le _ _
    · exact fun x ↦ le_rfl
    · exact Eventually.of_forall (truncateValue_tendsto u)
  · obtain ⟨C,hC,hbound⟩ := valueCutoffSlope_bounded
    let B := max C 1
    have hB : 0≤B := le_trans hC (le_max_left _ _)
    have hu1 : ContDiff ℝ 1 u := hu.of_le (by simp)
    have hgu : MemLp (cellGradient u) 2 volume :=
      (continuous_cellGradient hu1).memLp_of_hasCompactSupport (OAI.Analysis.PDE.Weak.hasCompactSupport_cellGradient hc)
    apply tendsto_toL2_of_dominated (fun n ↦ cellGradient (v n)) (cellGradient u)
      (fun n ↦ (continuous_cellGradient ((hv n).of_le (by simp))).memLp_of_hasCompactSupport
        (OAI.Analysis.PDE.Weak.hasCompactSupport_cellGradient (hvc n))) hgu
      (fun x ↦ B*‖cellGradient u x‖) (hgu.norm.const_mul B)
    · intro n x
      rw [cellGradient_truncateValue hu1,norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((hbound _).trans (le_max_left _ _)) (norm_nonneg _)
    · intro x
      exact le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _)
    · exact cellGradient_truncateValue_tendsto hu1

end OAI.Analysis.PDE.Variational
