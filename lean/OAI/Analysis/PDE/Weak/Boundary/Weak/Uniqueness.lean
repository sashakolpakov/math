import OAI.Analysis.PDE.Weak.Boundary.Weak.Scalar
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Uniqueness of genuine scalar weak derivatives on an open set. -/
theorem HasWeakDirectionalDerivativeOn.scalar_unique
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    {u g h : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} {v : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hdg : HasWeakDirectionalDerivativeOn volume Ω v u g)
    (hdh : HasWeakDirectionalDerivativeOn volume Ω v u h) :
    ∀ᵐ x ∂volume, x ∈ Ω → g x = h x := by
  have hl : LocallyIntegrableOn (fun x => g x - h x) Ω volume :=
    ((hg.sub hh).locallyIntegrable (by norm_num)).locallyIntegrableOn Ω
  have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hl ?_
  · filter_upwards [hz] with x hx
    exact fun hxs => sub_eq_zero.mp (hx hxs)
  intro φ hφ hs hsub
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hs
  have eg := hdg.scalar_identity volume φ (hφ.of_le (by simp)) hs hsub
  have eh := hdh.scalar_identity volume φ (hφ.of_le (by simp)) hs hsub
  simp only [smul_eq_mul, mul_sub]
  rw [integral_sub (μ := volume) (f := fun x => φ x * g x)
    (g := fun x => φ x * h x) (hφ2.integrable_mul hg) (hφ2.integrable_mul hh)]
  have eg' : (∫ x, φ x * g x) = -(∫ x, u x * fderiv ℝ φ x v) := by
    simpa only [mul_comm] using eg
  have eh' : (∫ x, φ x * h x) = -(∫ x, u x * fderiv ℝ φ x v) := by
    simpa only [mul_comm] using eh
  rw [eg', eh', sub_self]

/-- Componentwise uniqueness gives uniqueness of the full gradient derivative. -/
theorem HasWeakDirectionalDerivativeOn.vector_unique
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    {u g h : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m} {v : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hdg : HasWeakDirectionalDerivativeOn volume Ω v u g)
    (hdh : HasWeakDirectionalDerivativeOn volume Ω v u h) :
    ∀ᵐ x ∂volume, x ∈ Ω → g x = h x := by
  have hc (j : Fin (m + 1)) := OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.scalar_unique hΩ
    (memLp_cell_component hg j) (memLp_cell_component hh j)
    (hdg.scalar_component j) (hdh.scalar_component j)
  filter_upwards [ae_all_iff.mpr hc] with x hx
  intro hxs
  ext j
  exact hx j hxs

end OAI.Analysis.PDE.Weak
