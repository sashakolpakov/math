import OAI.Analysis.PDE.Green.LocalExtension
import OAI.Analysis.Calculus.Current.Physical.Compact

/-! Smooth global extensions of the actual physical fiber geometry.  The
extensions preserve the exact sublevel sets; every quantitative estimate is
taken on the original sublevel, where their germs are unchanged. -/

open Set Filter
open scoped Topology

namespace OAI.Analysis.PDE.Green

open OAI.Analysis.Calculus.Current

theorem exists_physical_global_extensions {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) :
    ∃ (R : (Option (Fin d) → ℂ) → ℝ)
      (V : (Option (Fin d) → ℂ) → (Option (Fin d) → ℂ)),
      ContDiff ℝ 3 R ∧ ContDiff ℝ 3 V ∧
      (∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
        R =ᶠ[𝓝 q] OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ ∧
        V =ᶠ[𝓝 q] OAI.Analysis.Calculus.Current.physicalRadialField τ) ∧
      (∀ q, R q < 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0) ∧
      (∀ q, R q ≤ 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) := by
  let K : Set (Option (Fin d) → ℂ) :=
    {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 1}
  have hK : IsCompact K := OAI.Analysis.Calculus.Current.isCompact_physical_fiber_sublevel a τ ha ht 1 le_rfl
  have hU := OAI.Analysis.Calculus.Current.isOpen_physicalRegularDomain (d := d) τ
  have hKU : K ⊆ OAI.Analysis.Calculus.Current.physicalRegularDomain τ := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
  obtain ⟨R, hR, hReq, hRneg, hRnonpos⟩ :=
    exists_global_sublevel_extension (k := (3 : ℕ∞)) hU
      ((OAI.Analysis.Calculus.Current.contDiffOn_physicalFiberDefining (d := d) (1 / 10) a τ).of_le (by norm_num))
      (show (0 : ℝ) ≤ 1 by norm_num) hK hKU
  obtain ⟨χ, hχ, hχrange, hχone, hχzero⟩ :=
    exists_smooth_cutoff_near_compact (k := (3 : ℕ∞)) hK hU hKU
  let V := fun q => χ q • OAI.Analysis.Calculus.Current.physicalRadialField (d := d) τ q
  have hV : ContDiff ℝ 3 V := contDiff_cutoff_smul hU hχ hχzero
    ((OAI.Analysis.Calculus.Current.contDiffOn_physicalRadialField (d := d) τ).of_le (by norm_num))
  refine ⟨R, V, hR, hV, ?_, hRneg, hRnonpos⟩
  intro q hq
  refine ⟨hReq q hq, ?_⟩
  have hqK : q ∈ K := hq.trans (by norm_num)
  filter_upwards [hχone q hqK] with p hp
  simp only [V, hp, one_smul]

/-- The extension constants depend only on dimension, not on the small fiber
scale or on time within the source strip. -/
theorem exists_physical_bounded_extensions (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (τ : ℂ), 0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 →
    ∃ (R : (Option (Fin d) → ℂ) → ℝ)
      (V : (Option (Fin d) → ℂ) → (Option (Fin d) → ℂ)),
      ContDiff ℝ 3 R ∧ ContDiff ℝ 3 V ∧
      (∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
        R =ᶠ[𝓝 q] OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ ∧
        V =ᶠ[𝓝 q] OAI.Analysis.Calculus.Current.physicalRadialField τ) ∧
      (∀ q, R q < 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0) ∧
      (∀ q, R q ≤ 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) ∧
      (∀ q, R q ≤ 0 →
        1 ≤ fderiv ℝ R q (V q) + (R q) ^ 2 ∧
        ‖fderiv ℝ V q‖ ≤ C ∧ ‖R q‖ ≤ 1 ∧ ‖q‖ ≤ 28) := by
  obtain ⟨C, hC, hbound⟩ := OAI.Analysis.Calculus.Current.physicalRadialField_uniform_bounds d
  refine ⟨C, hC, ?_⟩
  intro a τ ha ht ht'
  obtain ⟨R, V, hR, hV, heq, hneg, hnonpos⟩ :=
    exists_physical_global_extensions (d := d) a τ ha ht
  refine ⟨R, V, hR, hV, heq, hneg, hnonpos, ?_⟩
  intro q hq
  have hq' := (hnonpos q).mp hq
  obtain ⟨heR, heV⟩ := heq q hq'
  have hRq := heR.eq_of_nhds
  have hVq := heV.eq_of_nhds
  have hdR : fderiv ℝ R q = fderiv ℝ (OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ) q := heR.fderiv_eq
  have hdV : fderiv ℝ V q = fderiv ℝ (OAI.Analysis.Calculus.Current.physicalRadialField τ) q := heV.fderiv_eq
  have hreg := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
    (show OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 1 from hq'.trans (by norm_num))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdR, hRq, hVq]
    exact OAI.Analysis.Calculus.Current.physical_radial_transverse_coefficient a τ q hreg.1 hq'
  · rw [hdV]
    exact (hbound a τ q ha ht ht' hq').2
  · rw [hRq, Real.norm_eq_abs]
    exact abs_le.mpr ⟨OAI.Analysis.Calculus.Current.physicalFiberDefining_ge_neg_one (1 / 10) a τ q,
      hq'.trans (by norm_num)⟩
  · have hb := OAI.Analysis.Calculus.Current.physical_fiber_collar_norm_bound a τ q ha ht
      (hq'.trans (show (0 : ℝ) ≤ 1 by norm_num))
    linarith

end OAI.Analysis.PDE.Green
