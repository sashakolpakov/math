import OAI.Analysis.PDE.Weak.Elliptic.Pairing

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem hasCompactSupport_differenceQuotient {u : X → ℝ}
    (hu : HasCompactSupport u) (v : X) (h : ℝ) :
    HasCompactSupport (differenceQuotient v h u) := by
  have ht := hu.comp_isClosedEmbedding (Homeomorph.addRight (h • v)).isClosedEmbedding
  have hs := ht.sub hu
  exact hs.comp_left (by simp : h⁻¹ • (0 : ℝ) = 0)

theorem tsupport_differenceQuotient_subset (u : X → ℝ) (v : X) (h : ℝ) :
    tsupport (differenceQuotient v h u) ⊆
      (fun x ↦ x + h • v) ⁻¹' tsupport u ∪ tsupport u := by
  have hs := (tsupport_smul_subset_right (fun _ : X ↦ h⁻¹)
    (fun x ↦ u (x + h • v) - u x)).trans
      (tsupport_sub (fun x ↦ u (x + h • v)) u)
  have ht : tsupport (fun x ↦ u (x + h • v)) =
      (fun x ↦ x + h • v) ⁻¹' tsupport u :=
    tsupport_comp_eq_preimage u (Homeomorph.addRight (h • v))
  rwa [ht] at hs

open OAI.Analysis.PDE.Variational
variable {m : ℕ}

theorem hasCompactSupport_cellGradient {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hu : HasCompactSupport u) : HasCompactSupport (OAI.Analysis.PDE.Variational.cellGradient u) := by
  have hd : HasCompactSupport (fderiv ℝ u) := hu.fderiv (𝕜 := ℝ)
  let T : (OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ) → OAI.Analysis.PDE.Variational.CellVectors m :=
    fun L ↦ WithLp.toLp 2 (fun i ↦ L (Pi.single i 1))
  have ht : T 0 = 0 := by ext i; simp [T]
  exact hd.comp_left ht

theorem integrable_inner_of_memLp {Y V : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {μ : Measure Y}
    {f g : Y → V} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun y ↦ inner ℝ (f y) (g y)) μ := by
  apply (L2.integrable_inner (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- Distributional divergence equation against genuine smooth compactly
supported tests in the open domain. -/
def WeakDivergenceEquation (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m))
    (H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m) (f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) : Prop :=
  ∀ φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ Ω →
      (∫ x, inner ℝ (H x) (OAI.Analysis.PDE.Variational.cellGradient φ x)) = ∫ x, f x * φ x

theorem WeakDivergenceEquation.differenceQuotient {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    {H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m} {f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hweak : WeakDivergenceEquation Ω H f) (hH : MemLp H 2 volume)
    (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ) (w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hw : ContDiff ℝ ∞ w) (hws : HasCompactSupport w)
    (hΩ : tsupport w ⊆ Ω)
    (hΩshift : (fun x ↦ x + (-h) • v) ⁻¹' tsupport w ⊆ Ω) :
    (∫ x, inner ℝ (differenceQuotient v h H x) (OAI.Analysis.PDE.Variational.cellGradient w x)) =
      -(∫ x, f x * differenceQuotient v (-h) w x) := by
  have hgrad : MemLp (OAI.Analysis.PDE.Variational.cellGradient w) 2 volume :=
    (OAI.Analysis.PDE.Variational.continuous_cellGradient (hw.of_le (by simp))).memLp_of_hasCompactSupport
      (hasCompactSupport_cellGradient hws)
  apply shifted_weak_equation v h H f w (hw.differentiable (by simp))
  · exact integrable_inner_of_memLp hH hgrad
  · exact integrable_inner_of_memLp
      (hH.comp_measurePreserving (measurePreserving_add_right volume (h • v))) hgrad
  · apply hweak _ (contDiff_differenceQuotient v (-h) hw)
      (hasCompactSupport_differenceQuotient hws v (-h))
    exact (tsupport_differenceQuotient_subset w v (-h)).trans (union_subset hΩshift hΩ)

end OAI.Analysis.PDE.Weak
