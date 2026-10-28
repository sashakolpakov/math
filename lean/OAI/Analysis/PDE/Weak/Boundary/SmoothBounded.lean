import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedCoordinateDerivative_map (L : E →L[ℝ] F)
    {f : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hf : ContDiff ℝ ∞ f)
    (α : List (Fin (m + 1))) :
    iteratedCoordinateDerivative α (fun x => L (f x)) =
      fun x => L (iteratedCoordinateDerivative α f x) := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    simp only [iteratedCoordinateDerivative, ih]
    funext x
    have hd := L.hasFDerivAt.comp x
      ((contDiff_iteratedCoordinateDerivative hf α).differentiable (by simp) x).hasFDerivAt
    exact congrArg (fun T => T (Pi.single i 1)) hd.fderiv

theorem SmoothBounded.map (L : E →L[ℝ] F) {f : OAI.Analysis.PDE.Variational.CellCoordinates m → E}
    (hf : SmoothBounded f) : SmoothBounded (fun x => L (f x)) := by
  refine ⟨L.contDiff.comp hf.1, ?_⟩
  intro α
  obtain ⟨C, hC⟩ := hf.2 α
  refine ⟨‖L‖ * C, ?_⟩
  intro x
  rw [iteratedCoordinateDerivative_map L hf.1]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg L))

/-- A smooth function which is constant outside a compact set has all
coordinate derivatives bounded. -/
theorem smoothBounded_of_eq_const_off_compact
    {f : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hf : ContDiff ℝ ∞ f)
    {K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hK : IsCompact K) (c : E)
    (he : ∀ x ∉ K, f x = c) : SmoothBounded f := by
  have hs : HasCompactSupport (fun x => f x - c) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (sub_eq_zero.mpr (he x hn))
  have hb := (smoothBounded_of_hasCompactSupport (hf.sub contDiff_const) hs).add
    (smoothBounded_const c)
  have heq : ((fun x => f x - c) + fun x => c) = f := by
    funext x
    simp only [Pi.add_apply, sub_add_cancel]
  rwa [heq] at hb

theorem smoothBounded_inv_of_eq_const_off_compact
    {a : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (ha : ContDiff ℝ ∞ a) (hne : ∀ x, a x ≠ 0)
    {K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hK : IsCompact K) (c : ℝ)
    (he : ∀ x ∉ K, a x = c) : SmoothBounded (fun x => (a x)⁻¹) := by
  exact smoothBounded_of_eq_const_off_compact (ha.inv hne) hK c⁻¹
    (fun x hx => congrArg Inv.inv (he x hx))

end OAI.Analysis.PDE.Weak
