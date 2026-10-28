import OAI.Analysis.PDE.Concentration.WeightedLattice
import OAI.Analysis.PDE.Green.Localized.Green

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter _root_.MeasureTheory OAI.Analysis.PDE.Green
open scoped Topology

theorem integral_divergence_euclidean_lattice_localized
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : ι → EuclideanSpace ℝ ι → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : EuclideanSpace ℝ ι → ℝ} (hr : ContDiff ℝ 2 r)
    (hreg : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ ∀ᶠ y in 𝓝 x, ∀ i, F i y = 0)
    (hzero : ∀ x, r x = 0 →
      ∑ i, fderiv ℝ r x (EuclideanSpace.single i 1) * F i x = 0)
    (hface : CompatibleLatticeFaces c L a b r F) :
    (∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) = 0 := by
  let q := fun x => ∑ i, fderiv ℝ r x (EuclideanSpace.single i 1) * F i x
  have hq : ContDiff ℝ 1 q := ContDiff.sum (fun i _ =>
    ((hr.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).mul (hF i))
  have hregq : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ q =ᶠ[𝓝 x] (fun _ => 0) := by
    intro x hx hz
    rcases hreg x hx hz with h | h
    · exact Or.inl h
    · apply Or.inr
      filter_upwards [h] with y hy
      simp only [q, hy, mul_zero, Finset.sum_const_zero]
  have hcompact : IsCompact (euclideanLatticeCell c L a b) :=
    (OAI.Analysis.PDE.Green.euclideanCoordinates c).toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.image L.continuous)
  obtain ⟨C, hC0, hC⟩ := OAI.Analysis.PDE.Green.regular_or_locally_zero_compact_bound hcompact
    (hr.of_le (by norm_num)) hq hregq hzero
  have hh := weighted_euclidean_lattice_divergence_bound c L a b hab F hF
    (hr.of_le (by norm_num)) (continuous_const : Continuous (fun _ : EuclideanSpace ℝ ι => (0 : ℝ)))
    (ε := 0) (W := 0) (C := C) le_rfl (by intro k; simp)
    (by intro x hx; simpa only [norm_zero, mul_zero, zero_add] using hC x hx) hface
  apply norm_le_zero_iff.mp
  simpa only [zero_mul, mul_zero] using hh

end OAI.Analysis.PDE.Concentration
