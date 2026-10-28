import OAI.Analysis.PDE.Elliptic.Boundary.SmoothInverse
import OAI.Analysis.PDE.Weak.Boundary.NormalCoordinates

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational OAI.Analysis.PDE.Elliptic

variable {m : ℕ}

/-- A bounded genuine smooth chart taking the positive coordinate
halfspace exactly to the negative side of a regular defining function. -/
theorem exists_smooth_boundary_chart
    (r : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hr : ContDiff ℝ ∞ r)
    (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (hreg : fderiv ℝ r x ≠ 0) :
    ∃ (k : Fin (m+1)) (U V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m))
      (G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m),
      IsOpen U ∧ IsOpen V ∧ Bornology.IsBounded U ∧ Bornology.IsBounded V ∧
      0 ∈ U ∧ x ∈ V ∧ ContDiff ℝ ∞ G ∧ ContDiff ℝ ∞ P ∧ G 0 = x ∧ P x = 0 ∧
      MapsTo G U V ∧ MapsTo P V U ∧
      (∀ y ∈ U, P (G y) = y) ∧ (∀ z ∈ V, G (P z) = z) ∧
      (∀ y ∈ U, r (G y) - r x = -y k) := by
  let g := fderiv ℝ r x
  obtain ⟨w, hw⟩ := LinearMap.range_eq_top.mp (OAI.Analysis.PDE.Dirichlet.real_linear_form_range_top g hreg) 1
  let P₀ := OAI.Analysis.PDE.Elliptic.flatteningMap r x g w
  have hP₀ : ContDiff ℝ ∞ P₀ := OAI.Analysis.PDE.Elliptic.contDiff_flatteningMap hr x g w
  have hP₀x : P₀ x = 0 := OAI.Analysis.PDE.Elliptic.flatteningMap_base r x g w
  have hdP₀ : HasFDerivAt P₀ (ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Variational.CellCoordinates m)) x :=
    OAI.Analysis.PDE.Elliptic.hasFDerivAt_flatteningMap (hr.differentiable (by simp) x).hasFDerivAt w
  obtain ⟨G₀, R, V, hG₀, hR, hV, hVb, hxV, hG₀0, hG₀V, hP₀U, hPG, hGP⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_smooth_inverse_chart P₀ hP₀ x hP₀x hdP₀
  obtain ⟨k, L, hL⟩ := exists_coordinate_normalizer g hreg
  let U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m) := L.symm ⁻¹' ball 0 R
  let G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m := fun y => G₀ (L.symm y)
  let P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m := fun z => L (P₀ z)
  have hUb : Bornology.IsBounded U := by
    apply ((isCompact_closedBall (0 : OAI.Analysis.PDE.Variational.CellCoordinates m) R).image L.continuous).isBounded.subset
    intro y hy
    exact ⟨L.symm y, ball_subset_closedBall hy, L.apply_symm_apply y⟩
  refine ⟨k, U, V, G, P, isOpen_ball.preimage L.symm.continuous, hV, hUb, hVb,
    ?_, hxV, hG₀.comp L.symm.contDiff, L.contDiff.comp hP₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change L.symm 0 ∈ ball 0 R
    simpa only [map_zero] using (mem_ball_self hR : (0 : OAI.Analysis.PDE.Variational.CellCoordinates m) ∈ ball 0 R)
  · simpa only [G, map_zero] using hG₀0
  · simp only [P, hP₀x, map_zero]
  · exact fun y hy => hG₀V hy
  · intro z hz
    change L.symm (L (P₀ z)) ∈ ball 0 R
    simpa only [L.symm_apply_apply] using hP₀U hz
  · intro y hy
    change L (P₀ (G₀ (L.symm y))) = y
    rw [hPG _ hy, L.apply_symm_apply]
  · intro z hz
    change G₀ (L.symm (L (P₀ z))) = z
    rw [L.symm_apply_apply, hGP _ hz]
  · intro y hy
    have he := OAI.Analysis.PDE.Elliptic.flatteningMap_level r x g w hw (G₀ (L.symm y))
    change g (P₀ (G₀ (L.symm y))) = r (G y) - r x at he
    rw [hPG _ hy] at he
    have hn := hL (L.symm y)
    rw [L.apply_symm_apply] at hn
    linarith

end OAI.Analysis.PDE.Weak
