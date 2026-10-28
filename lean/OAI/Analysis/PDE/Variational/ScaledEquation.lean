import OAI.Analysis.PDE.Variational.FluxProduct
import OAI.Analysis.PDE.Variational.LocalizedEquation

open Set _root_.MeasureTheory InnerProductSpace Filter
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

/-- Moving a smooth compact multiplier onto a divergence equation only
introduces the usual first-order commutator. The conclusion is valid on
the whole domain, not just on the plateau of the cutoff. -/
theorem weakEquation_scaled {Ω V : Set (CellCoordinates m)}
    {H : CellCoordinates m → CellVectors m} {f : CellCoordinates m → ℝ}
    (hH : MemLp H 2 volume) (hf : MemLp f 2 volume)
    (hweak : OAI.Analysis.PDE.Weak.WeakDivergenceEquation (Ω∩V) H f)
    (η : CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η)
    (hs : HasCompactSupport η) (hV : tsupport η⊆V) :
    OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω (fun x ↦ η x • H x)
      (fun x ↦ η x*f x-inner ℝ (H x) (cellGradient η x)) := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hηH := memLp_smul_compact_left hH hη.continuous hs
  have hηf := memLp_mul_compact_left hf hη.continuous hs
  have hc := memLp_inner_compact_right hH (continuous_cellGradient hη1)
    (OAI.Analysis.PDE.Weak.hasCompactSupport_cellGradient hs)
  intro φ hφ hφs hsub
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport (p:=2) hφs
  have hgφ : MemLp (cellGradient φ) 2 volume := (continuous_cellGradient (hφ.of_le (by simp))).memLp_of_hasCompactSupport
    (p:=2) (OAI.Analysis.PDE.Weak.hasCompactSupport_cellGradient hφs)
  have hi := OAI.Analysis.PDE.Weak.integrable_inner_of_memLp hηH hgφ
  have hj : Integrable (fun x ↦ inner ℝ (H x) (cellGradient η x)*φ x) := hc.integrable_mul hφ2
  have hk : Integrable (fun x ↦ (η x*f x)*φ x) := hηf.integrable_mul hφ2
  have he := hweak (fun x ↦ η x*φ x) (hη.mul hφ) hs.mul_right (by
    intro x hx
    exact ⟨hsub (tsupport_mul_subset_right hx),hV (tsupport_mul_subset_left hx)⟩)
  have heleft : (∫ x, inner ℝ (H x) (cellGradient (fun y ↦ η y*φ y) x)) =
      (∫ x, inner ℝ (η x • H x) (cellGradient φ x)) +
      ∫ x, inner ℝ (H x) (cellGradient η x)*φ x := by
    have heq x : inner ℝ (H x) (cellGradient (fun y ↦ η y*φ y) x) =
        inner ℝ (η x • H x) (cellGradient φ x) + inner ℝ (H x) (cellGradient η x)*φ x := by
      rw [OAI.Analysis.PDE.Weak.cellGradient_mul (hη.differentiable (by simp)) (hφ.differentiable (by simp))]
      simp only [inner_add_right, real_inner_smul_left, real_inner_smul_right]
      ring
    simp_rw [heq]
    exact integral_add hi hj
  have heright : (∫ x, f x*(η x*φ x)) = ∫ x, (η x*f x)*φ x := by
    congr 1
    funext x
    ring
  rw [heleft,heright] at he
  simp_rw [sub_mul]
  rw [integral_sub hk hj]
  linarith

theorem weakEquation_add {Ω : Set (CellCoordinates m)}
    {H R : CellCoordinates m → CellVectors m} {f r : CellCoordinates m → ℝ}
    (hH : MemLp H 2 volume) (hR : MemLp R 2 volume)
    (hf : MemLp f 2 volume) (hr : MemLp r 2 volume)
    (he : OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω H f) (heR : OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω R r) :
    OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω (fun x ↦ H x+R x) (fun x ↦ f x+r x) := by
  intro φ hφ hs hsub
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport (p:=2) hs
  have hgφ : MemLp (cellGradient φ) 2 volume := (continuous_cellGradient (hφ.of_le (by simp))).memLp_of_hasCompactSupport
    (p:=2) (OAI.Analysis.PDE.Weak.hasCompactSupport_cellGradient hs)
  have hfi : Integrable (fun x ↦ f x*φ x) := hf.integrable_mul hφ2
  have hri : Integrable (fun x ↦ r x*φ x) := hr.integrable_mul hφ2
  simp_rw [inner_add_left,add_mul]
  rw [integral_add (OAI.Analysis.PDE.Weak.integrable_inner_of_memLp hH hgφ) (OAI.Analysis.PDE.Weak.integrable_inner_of_memLp hR hgφ),
    integral_add hfi hri,
    he φ hφ hs hsub,heR φ hφ hs hsub]

end OAI.Analysis.PDE.Variational
