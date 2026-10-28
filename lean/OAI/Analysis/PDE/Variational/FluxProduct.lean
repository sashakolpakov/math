import OAI.Analysis.PDE.Variational.H1Divergence
import OAI.Analysis.PDE.Weak.Elliptic.Cutoff

open Set _root_.MeasureTheory InnerProductSpace Filter
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

theorem memLp_inner_compact_right
    {u B : CellCoordinates m → CellVectors m} (hu : MemLp u 2 volume)
    (hB : Continuous B) (hs : HasCompactSupport B) :
    MemLp (fun x ↦ inner ℝ (u x) (B x)) 2 volume := by
  obtain ⟨C,hC⟩ := (hs.isCompact_range hB).isBounded.exists_norm_le
  apply hu.of_le_mul (c:=C) (hu.aestronglyMeasurable.inner hB.aestronglyMeasurable)
  filter_upwards with x
  exact (norm_inner_le_norm _ _).trans (by
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _ (mem_range_self x)) (norm_nonneg _))

theorem memLp_mul_compact_left
    {u a : CellCoordinates m → ℝ} (hu : MemLp u 2 volume)
    (ha : Continuous a) (hs : HasCompactSupport a) :
    MemLp (fun x ↦ a x*u x) 2 volume := by
  obtain ⟨C,hC⟩ := (hs.isCompact_range ha).isBounded.exists_norm_le
  apply hu.of_le_mul (c:=C) (ha.aestronglyMeasurable.mul hu.aestronglyMeasurable)
  filter_upwards with x
  change ‖a x*u x‖≤C*‖u x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC _ (mem_range_self x)) (norm_nonneg _)

theorem memLp_smul_compact_right
    {u : CellCoordinates m → ℝ} {B : CellCoordinates m → CellVectors m}
    (hu : MemLp u 2 volume) (hB : Continuous B) (hs : HasCompactSupport B) :
    MemLp (fun x ↦ u x • B x) 2 volume := by
  obtain ⟨C,hC⟩ := (hs.isCompact_range hB).isBounded.exists_norm_le
  apply hu.of_le_mul (c:=C) (hu.aestronglyMeasurable.smul hB.aestronglyMeasurable)
  filter_upwards with x
  change ‖u x • B x‖≤C*‖u x‖
  rw [norm_smul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC _ (mem_range_self x)) (norm_nonneg _)

theorem memLp_smul_compact_left
    {u : CellCoordinates m → CellVectors m} {a : CellCoordinates m → ℝ}
    (hu : MemLp u 2 volume) (ha : Continuous a) (hs : HasCompactSupport a) :
    MemLp (fun x ↦ a x • u x) 2 volume := by
  obtain ⟨C,hC⟩ := (hs.isCompact_range ha).isBounded.exists_norm_le
  apply hu.of_le_mul (c:=C) (ha.aestronglyMeasurable.smul hu.aestronglyMeasurable)
  filter_upwards with x
  change ‖a x • u x‖≤C*‖u x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC _ (mem_range_self x)) (norm_nonneg _)

/-- The divergence of the product of an actual H¹ value and a compact C¹
vector field. No second derivative of the H¹ value is used. -/
theorem h1_integral_flux_product {Ω : Set (CellCoordinates m)} {p : OAI.Analysis.PDE.Weak.H1Pair m}
    (hp : p∈OAI.Analysis.PDE.Weak.H1Zero Ω) (B : CellCoordinates m → CellVectors m)
    (hB : ContDiff ℝ 1 B) (hs : HasCompactSupport B)
    (φ : CellCoordinates m → ℝ) (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ) :
    (∫ x, inner ℝ (p.1 x • B x) (cellGradient φ x)) =
      -(∫ x, (inner ℝ (p.2 x) (B x) + p.1 x * cellDivergence B x)*φ x) := by
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφs
  have hgφ : MemLp (cellGradient φ) 2 volume :=
    (continuous_cellGradient hφ).memLp_of_hasCompactSupport (OAI.Analysis.PDE.Weak.hasCompactSupport_cellGradient hφs)
  have hv := memLp_smul_compact_right (Lp.memLp p.1) hB.continuous hs
  have hleft := OAI.Analysis.PDE.Weak.integrable_inner_of_memLp hv hgφ
  have hfirst : Integrable (fun x ↦ inner ℝ (p.2 x) (B x)*φ x) :=
    (memLp_inner_compact_right (Lp.memLp p.2) hB.continuous hs).integrable_mul hφ2
  have hlast : Integrable (fun x ↦ (p.1 x*cellDivergence B x)*φ x) := by
    convert (memLp_mul_compact_left (Lp.memLp p.1) (continuous_cellDivergence hB)
      (hasCompactSupport_cellDivergence hs)).integrable_mul hφ2 using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have he := OAI.Analysis.PDE.Variational.H1Zero.integral_divergence hp (fun x ↦ φ x • B x) (hφ.smul hB) hφs.smul_right
  simp_rw [real_inner_smul_right, cellDivergence_smul (hB.differentiable one_ne_zero)
    (hφ.differentiable one_ne_zero), mul_add] at he
  have hleft' : Integrable (fun x ↦ p.1 x*inner ℝ (B x) (cellGradient φ x)) := by
    simpa only [real_inner_smul_left] using hleft
  have hlast' : Integrable (fun x ↦ p.1 x*(φ x*cellDivergence B x)) := by
    convert hlast using 1
    funext x
    ring
  rw [integral_add hleft' hlast'] at he
  have hfirsteq : (∫ x, φ x*inner ℝ (p.2 x) (B x)) =
      ∫ x, inner ℝ (p.2 x) (B x)*φ x := by congr 1; funext x; ring
  have hlasteq : (∫ x, p.1 x*(φ x*cellDivergence B x)) =
      ∫ x, (p.1 x*cellDivergence B x)*φ x := by congr 1; funext x; ring
  rw [hfirsteq,hlasteq] at he
  simp_rw [add_mul, real_inner_smul_left]
  rw [integral_add hfirst hlast]
  linarith

end OAI.Analysis.PDE.Variational
