import OAI.Analysis.PDE.Variational.ScaledEquation
import OAI.Analysis.PDE.Weak.Elliptic.Product

open Set _root_.MeasureTheory InnerProductSpace Filter
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

/-- The exact scalar forcing after localizing a divergence-form solution.
The sign convention is `-div(A ∇u)=f`. No symmetry of `A` is needed. -/
def cutoffDirichletLoad
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (η : CellCoordinates m → ℝ) (p : OAI.Analysis.PDE.Weak.H1Pair m) (f : CellCoordinates m → ℝ)
    (x : CellCoordinates m) : ℝ :=
  η x*f x - inner ℝ (A x (p.2 x)) (cellGradient η x) -
    inner ℝ (p.2 x) (A x (cellGradient η x)) -
    p.1 x*cellDivergence (fun y ↦ A y (cellGradient η y)) x

/-- Compact cutoff localization has an actual global L² scalar forcing.
The equation extends from the physical patch `Ω ∩ V` to the whole domain
`Ω`; the localized H¹ function is still in the genuine zero-boundary
graph closure. -/
theorem cutoffDirichlet_equation_L2
    {Ω V : Set (CellCoordinates m)} (p : OAI.Analysis.PDE.Weak.H1Pair m) (hp : p∈OAI.Analysis.PDE.Weak.H1Zero Ω)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : ContDiff ℝ 1 A) {M : ℝ} (hAM : ∀ x, ‖A x‖≤M)
    (f : Lp ℝ 2 (volume : Measure (CellCoordinates m)))
    (hweak : OAI.Analysis.PDE.Weak.WeakDivergenceEquation (Ω∩V) (fun x ↦ A x (p.2 x)) f)
    (η : CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η)
    (hs : HasCompactSupport η) (hV : tsupport η⊆V)
    {N K : ℝ} (hN : ∀ x, |η x|≤N) (hK : ∀ x, ‖cellGradient η x‖≤K) :
    let q := OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hN hK p
    q∈OAI.Analysis.PDE.Weak.H1Zero Ω ∧ ∃ F : Lp ℝ 2 (volume : Measure (CellCoordinates m)),
      F =ᵐ[volume] cutoffDirichletLoad A η p f ∧
      OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω (fun x ↦ A x (q.2 x)) F := by
  dsimp only
  refine ⟨OAI.Analysis.PDE.Weak.H1Zero.cutoff hp η hη hN hK inter_subset_right, ?_⟩
  let H : CellCoordinates m → CellVectors m := fun x ↦ A x (p.2 x)
  let B : CellCoordinates m → CellVectors m := fun x ↦ A x (cellGradient η x)
  have hH : MemLp H 2 volume := OAI.Analysis.PDE.Weak.fieldMultiplier_memLp A hA.continuous.aestronglyMeasurable
    (Eventually.of_forall hAM) p.2
  have hB : ContDiff ℝ 1 B := hA.clm_apply ((OAI.Analysis.PDE.Weak.contDiff_cellGradient hη).of_le (by simp))
  have hBs : HasCompactSupport B := OAI.Analysis.PDE.Weak.hasCompactSupport_operator_apply A (OAI.Analysis.PDE.Weak.hasCompactSupport_cellGradient hs)
  let g : CellCoordinates m → ℝ := fun x ↦ η x*f x-inner ℝ (H x) (cellGradient η x)
  let r : CellCoordinates m → ℝ := fun x ↦ -(inner ℝ (p.2 x) (B x)+p.1 x*cellDivergence B x)
  have hg : MemLp g 2 volume :=
    (memLp_mul_compact_left (Lp.memLp f) hη.continuous hs).sub
      (memLp_inner_compact_right hH (continuous_cellGradient (hη.of_le (by simp)))
        (OAI.Analysis.PDE.Weak.hasCompactSupport_cellGradient hs))
  have hd : MemLp (fun x ↦ p.1 x*cellDivergence B x) 2 volume := by
    simpa only [mul_comm] using memLp_mul_compact_left (Lp.memLp p.1)
      (continuous_cellDivergence hB) (hasCompactSupport_cellDivergence hBs)
  have hr : MemLp r 2 volume :=
    ((memLp_inner_compact_right (Lp.memLp p.2) hB.continuous hBs).add hd).neg
  have he1 : OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω (fun x ↦ η x • H x) g :=
    weakEquation_scaled hH (Lp.memLp f) hweak η hη hs hV
  have he2 : OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω (fun x ↦ p.1 x • B x) r := by
    intro φ hφ hφs _
    simpa only [r,neg_mul,integral_neg] using
      h1_integral_flux_product hp B hB hBs φ (hφ.of_le (by simp)) hφs
  have he := weakEquation_add (memLp_smul_compact_left hH hη.continuous hs)
    (memLp_smul_compact_right (Lp.memLp p.1) hB.continuous hBs) hg hr he1 he2
  let F := (hg.add hr).toLp (fun x ↦ g x+r x)
  have hFe : F =ᵐ[volume] fun x ↦ g x+r x := (hg.add hr).coeFn_toLp
  refine ⟨F,?_,?_⟩
  · filter_upwards [hFe] with x hx
    rw [hx]
    dsimp [g,r,H,B,cutoffDirichletLoad]
    ring
  · apply weakEquation_congr_on he (subset_refl _)
    · filter_upwards [OAI.Analysis.PDE.Weak.cutoffH1Pair_gradient_ae η (hη.of_le (by simp)) hN hK p] with x hx
      intro _
      rw [hx,map_add,map_smul,map_smul]
    · filter_upwards [hFe] with x hx
      exact fun _ ↦ hx

end OAI.Analysis.PDE.Variational
