import OAI.Analysis.PDE.Weak.Elliptic.Product
import OAI.Analysis.PDE.Weak.Boundary.NormalFlux

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Summing the actual weak coordinate derivatives gives an L²
divergence and its integration-by-parts identity. -/
theorem weak_negative_divergence
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {R : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m}
    (hR : MemLp R 2 volume) (G : Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m)
    (hG : ∀ i, MemLp (G i) 2 volume)
    (hder : ∀ i, HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) R (G i)) :
    MemLp (fun x ↦ -∑ i, G i x i) 2 volume ∧
      WeakDivergenceEquation Ω R (fun x ↦ -∑ i, G i x i) := by
  refine ⟨(memLp_finsetSum _ (fun i _ ↦ memLp_cell_component (hG i) i)).neg, ?_⟩
  intro φ hφ hs hsub
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hs
  have hD (i : Fin (m + 1)) : MemLp (fun x ↦ fderiv ℝ φ x (Pi.single i 1)) 2 volume :=
    (OAI.Analysis.PDE.Green.continuous_directional (hφ.of_le (by simp)) _).memLp_of_hasCompactSupport
      (hs.fderiv_apply ℝ _)
  have hi (i : Fin (m + 1)) : Integrable (fun x ↦ R x i * fderiv ℝ φ x (Pi.single i 1)) :=
    (memLp_cell_component hR i).integrable_mul (hD i)
  have hgφ (i : Fin (m + 1)) : Integrable (fun x ↦ G i x i * φ x) :=
    (memLp_cell_component (hG i) i).integrable_mul hφ2
  have hinner (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      inner ℝ (R x) (OAI.Analysis.PDE.Variational.cellGradient φ x) = ∑ i, R x i * fderiv ℝ φ x (Pi.single i 1) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, OAI.Analysis.PDE.Variational.cellGradient_apply]
    congr 1
    funext i
    ring
  simp_rw [hinner]
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  have he : (∑ i, ∫ x, R x i * fderiv ℝ φ x (Pi.single i 1)) =
      -∑ i, ∫ x, G i x i * φ x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hh := (hder i).component i φ (hφ.of_le (by simp)) hs hsub
    linarith
  rw [he]
  simp_rw [neg_mul, Finset.sum_mul]
  rw [integral_neg, integral_finsetSum _ (fun i _ ↦ hgφ i)]

theorem integrable_inner_memLp_test
    {H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m} (hH : MemLp H 2 volume)
    {φ : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m} (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun x ↦ inner ℝ (H x) (φ x)) := by
  apply (integrable_inner_compact_test volume (hH.toLp H) hφ hs).congr
  filter_upwards [hH.coeFn_toLp] with x hx
  rw [hx]

/-- Remove an explicitly known divergence flux from the equation. -/
theorem WeakDivergenceEquation.subtract_flux
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {H R : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m}
    {f r : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hweak : WeakDivergenceEquation Ω (fun x ↦ H x + R x) f)
    (hRder : WeakDivergenceEquation Ω R r)
    (hH : MemLp H 2 volume) (hR : MemLp R 2 volume)
    (hf : MemLp f 2 volume) (hr : MemLp r 2 volume) :
    WeakDivergenceEquation Ω H (fun x ↦ f x - r x) := by
  intro φ hφ hs hsub
  have hiH := integrable_inner_memLp_test hH
    (OAI.Analysis.PDE.Variational.continuous_cellGradient (hφ.of_le (by simp))) (hasCompactSupport_cellGradient hs)
  have hiR := integrable_inner_memLp_test hR
    (OAI.Analysis.PDE.Variational.continuous_cellGradient (hφ.of_le (by simp))) (hasCompactSupport_cellGradient hs)
  have hp : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hs
  have he := hweak φ hφ hs hsub
  have heR := hRder φ hφ hs hsub
  simp_rw [inner_add_left] at he
  rw [integral_add hiH hiR, heR] at he
  simp_rw [sub_mul]
  rw [integral_sub (f := fun x ↦ f x * φ x) (g := fun x ↦ r x * φ x)
    (hf.integrable_mul hp) (hr.integrable_mul hp)]
  linarith

end OAI.Analysis.PDE.Weak
