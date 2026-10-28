import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalStretch

/-! # Ellipsoid -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.Ellipsoid.Construction

noncomputable section

/-! Minkowski's theorem in orthogonally stretched balls, including a
criterion that forces the resulting lattice vector outside a given subspace. -/

open scoped Classical
open Set _root_.Module _root_.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem minkowski_of_covolume_lt_measure
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {S : Set E}
    (hsym : ∀ x ∈ S, -x ∈ S) (hconv : Convex ℝ S)
    (hvol : ENNReal.ofReal (ZLattice.covolume Λ μ) * 2 ^ finrank ℝ E < μ S) :
    ∃ x ∈ Λ, x ≠ 0 ∧ x ∈ S := by
  let b := Free.chooseBasis ℤ Λ
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hfund : IsAddFundamentalDomain Λ.toAddSubgroup F μ :=
    ZLattice.isAddFundamentalDomain b μ
  let : Countable Λ.toAddSubgroup := (inferInstance : Countable Λ)
  have hfinite : μ F ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)).measure_lt_top.ne
  have hF : ENNReal.ofReal (ZLattice.covolume Λ μ) = μ F := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ μ hfund]
    exact ENNReal.ofReal_toReal hfinite
  rw [hF] at hvol
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    hfund hsym hconv hvol
  exact ⟨x.val, x.property, fun he => hx0 (Subtype.ext he), hx⟩

theorem minkowski_outside_subspace
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (W : Submodule ℝ E)
    {ε a b : ℝ} (ha : 0 < a) (hb : 0 < b) (haε : a ≤ ε)
    (hgap : ∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖x‖)
    (hvol : ENNReal.ofReal (ZLattice.covolume Λ μ) * 2 ^ finrank ℝ E <
      ENNReal.ofReal (a ^ finrank ℝ W * b ^ finrank ℝ Wᗮ) * μ (Metric.ball 0 1)) :
    ∃ x ∈ Λ, x ∉ W ∧ ‖x‖ ≤ a + b := by
  let f := OrthogonalStretch.Construction.orthogonalStretch W a b
  let S := f '' Metric.ball 0 1
  have hsym : ∀ x ∈ S, -x ∈ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨-y, by simpa using hy, f.map_neg y⟩
  have hconv : Convex ℝ S := (convex_ball (0 : E) 1).linear_image f
  have hSvol : ENNReal.ofReal (ZLattice.covolume Λ μ) * 2 ^ finrank ℝ E < μ S := by
    rw [Measure.addHaar_image_linearMap, OrthogonalStretch.Construction.orthogonalStretch_det]
    simpa only [abs_of_pos (mul_pos (pow_pos ha _) (pow_pos hb _))] using hvol
  obtain ⟨x, hxΛ, hx0, y, hy, rfl⟩ :=
    minkowski_of_covolume_lt_measure Λ μ hsym hconv hSvol
  have hyn : ‖y‖ < 1 := by simpa using hy
  refine ⟨f y, hxΛ, ?_, ?_⟩
  · intro hw
    have hyW : y ∈ W := (OrthogonalStretch.Construction.orthogonalStretch_mem_iff W a hb.ne' y).mp hw
    have hsmall : ‖f y‖ < ε := by
      rw [show f y = a • y from OrthogonalStretch.Construction.orthogonalStretch_of_mem W a b hyW, norm_smul,
        Real.norm_eq_abs, abs_of_pos ha]
      exact (mul_lt_of_lt_one_right ha hyn).trans_le haε
    exact hsmall.not_ge (hgap (f y) hxΛ hx0)
  · exact (OrthogonalStretch.Construction.orthogonalStretch_norm_le W ha.le hb.le y).trans
      (by nlinarith [mul_nonneg (add_nonneg ha.le hb.le) (sub_nonneg.mpr hyn.le)])

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.Ellipsoid.Construction
