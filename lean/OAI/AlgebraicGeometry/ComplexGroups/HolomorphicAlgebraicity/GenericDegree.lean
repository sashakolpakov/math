import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericHolomorphicPolynomial
import Mathlib.Data.Finset.Max

/-! # Generic Degree -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericDegree.Constructions.GenericPolynomial

noncomputable section

/-!
# Generic degree of a bounded polynomial family

Among finitely many coefficient germs, take the last nonzero one. Higher
coefficients vanish on a common neighborhood, and this chosen coefficient
controls the degree wherever it is nonzero.
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

theorem exists_generic_degree {E : Type*} [TopologicalSpace E]
    {G : E → ℂ[X]} {x : E} {D : ℕ} (hD : ∀ y, (G y).natDegree ≤ D)
    (hn : ¬∀ᶠ y in 𝓝 x, G y = 0) :
    ∃ k : ℕ, k ≤ D ∧ (¬∀ᶠ y in 𝓝 x, (G y).coeff k = 0) ∧
      ∀ᶠ y in 𝓝 x, (G y).natDegree ≤ k := by
  classical
  let K := (Finset.range (D + 1)).filter (fun k => ¬∀ᶠ y in 𝓝 x, (G y).coeff k = 0)
  have hK : K.Nonempty := by
    by_contra hKe
    have hzero (k : Fin (D + 1)) : ∀ᶠ y in 𝓝 x, (G y).coeff k.val = 0 := by
      by_contra hk
      exact hKe ⟨k.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt, hk⟩⟩
    apply hn
    filter_upwards [eventually_all.mpr hzero] with y hy
    apply Polynomial.ext
    intro k
    rw [coeff_zero]
    by_cases hk : k < D + 1
    · exact hy ⟨k, hk⟩
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hD y) (by omega))
  let k := K.max' hK
  have hkK : k ∈ K := K.max'_mem hK
  have hkD : k ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hkK).1)
  have hkn : ¬∀ᶠ y in 𝓝 x, (G y).coeff k = 0 := (Finset.mem_filter.mp hkK).2
  have htail (j : Fin (D + 1)) : ∀ᶠ y in 𝓝 x, k < j.val → (G y).coeff j.val = 0 := by
    by_cases hkj : k < j.val
    · have hjzero : ∀ᶠ y in 𝓝 x, (G y).coeff j.val = 0 := by
        by_contra hj
        have hjK : j.val ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, hj⟩
        exact (K.le_max' j.val hjK).not_gt hkj
      exact hjzero.mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hkj h))
  refine ⟨k, hkD, hkn, ?_⟩
  filter_upwards [eventually_all.mpr htail] with y hy
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hkj
  by_cases hj : j < D + 1
  · exact hy ⟨j, hj⟩ hkj
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hD y) (by omega))

theorem not_eventually_zero_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hfn : ¬∀ᶠ y in 𝓝 x, f y = 0) (hgn : ¬∀ᶠ y in 𝓝 x, g y = 0) :
    ¬∀ᶠ y in 𝓝 x, f y * g y = 0 := by
  intro hprod
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hprod
  have h := HolomorphicIdentity.Constructions.Identity.eventually_zero_or_eventually_zero_of_mul (hU.inter hV) ⟨hx, hxV⟩
    (hf.mono inter_subset_left) (hg.mono inter_subset_left) (fun _ hy => hVsub hy.2)
  exact h.elim hfn hgn

/-- A holomorphic function that is nonzero as a germ has a dense nonzero
locus on some neighborhood of the base point. -/
theorem exists_dense_nonzero_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) (hn : ¬∀ᶠ y in 𝓝 x, f y = 0) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      V ⊆ closure {y | y ∈ V ∧ f y ≠ 0} := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let V := Metric.ball x (R / 2)
  have hVU : V ⊆ U := (Metric.ball_subset_ball (by linarith)).trans hball
  refine ⟨V, Metric.isOpen_ball, Metric.mem_ball_self (by linarith), hVU, ?_⟩
  intro y hy
  have hyn : ¬∀ᶠ z in 𝓝 y, f z = 0 := by
    intro hyzero
    have hsub : Metric.ball y (R / 2) ⊆ U := by
      apply Subset.trans (Metric.ball_subset_ball' (show R / 2 + dist y x ≤ R from by
        have hdist := Metric.mem_ball.mp hy
        linarith)) hball
    have hident := HolomorphicIdentity.Constructions.Identity.eqOn_zero_ball_of_eventually_zero (hf.mono hsub) hyzero
    have hxy : x ∈ Metric.ball y (R / 2) := by
      rw [Metric.mem_ball, dist_comm]
      exact Metric.mem_ball.mp hy
    apply hn
    filter_upwards [Metric.isOpen_ball.mem_nhds hxy] with z hz
    exact hident hz
  apply mem_closure_iff_frequently.mpr
  exact ((not_eventually.mp hyn).and_eventually (Metric.isOpen_ball.mem_nhds hy)).mono
    (fun _ h => ⟨h.2, h.1⟩)

/-- Away from one genuine holomorphic exceptional zero set, common roots
are represented by a monic polynomial of one fixed degree. -/
theorem exists_monic_generic_family
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]
    (P : ι → E → ℂ[X]) {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (d : ℕ)
    (hcoeff : ∀ i k, DifferentiableOn ℂ (fun y => (P i y).coeff k) U)
    (hdegree : ∀ i y, y ∈ U → (P i y).natDegree ≤ d)
    (hnever : ∀ y ∈ U, ∃ i, P i y ≠ 0) :
    ∃ (k : ℕ) (Q : E → ℂ[X]) (c : E → ℂ) (V : Set E),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ DifferentiableOn ℂ c V ∧
      (¬∀ᶠ y in 𝓝 x, c y = 0) ∧
      (∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) {y | y ∈ V ∧ c y ≠ 0}) ∧
      ∀ y ∈ V, c y ≠ 0 → (Q y).Monic ∧ (Q y).natDegree = k ∧
        ∀ z : ℂ, (∀ i, (P i y).eval z = 0) ↔ (Q y).eval z = 0 := by
  obtain ⟨D, G, c, V, hV, hxV, hVU, hGdeg, hGcoeff, hc, hcn, hroot⟩ :=
    GenericHolomorphicPolynomial.Constructions.GenericPolynomial.exists_generic_common_root_family P hU hx d hcoeff hdegree (hnever x hx)
  have hGn (y : E) (hy : y ∈ V) (hcy : c y ≠ 0) : G y ≠ 0 := by
    intro hGy
    obtain ⟨i, hi⟩ := hnever y (hVU hy)
    apply hi
    apply Polynomial.zero_of_eval_zero
    intro z
    exact ((hroot y hy hcy z).mpr (by simp only [hGy, eval_zero])) i
  have hGgerm : ¬∀ᶠ y in 𝓝 x, G y = 0 := by
    intro hGzero
    apply hcn
    filter_upwards [hGzero, hV.mem_nhds hxV] with y hy hyV
    by_contra hcy
    exact hGn y hyV hcy hy
  obtain ⟨k, _, hkn, hkdeg⟩ := exists_generic_degree hGdeg hGgerm
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hkdeg
  let c' : E → ℂ := fun y => c y * (G y).coeff k
  let Q : E → ℂ[X] := fun y => ((G y).coeff k)⁻¹ • G y
  have hc'n : ¬∀ᶠ y in 𝓝 x, c' y = 0 :=
    not_eventually_zero_mul hV hxV hc (hGcoeff k) hcn hkn
  have hgood (y : E) (hy : c' y ≠ 0) : c y ≠ 0 ∧ (G y).coeff k ≠ 0 := mul_ne_zero_iff.mp hy
  refine ⟨k, Q, c', V ∩ W, hV.inter hW, ⟨hxV, hxW⟩,
    fun _ hy => hVU hy.1, (hc.fun_mul (hGcoeff k)).mono inter_subset_left, hc'n, ?_, ?_⟩
  · intro j
    have hsub : {y | y ∈ V ∩ W ∧ c' y ≠ 0} ⊆ V := fun _ hy => hy.1.1
    simp only [Q, coeff_smul, smul_eq_mul]
    exact ((hGcoeff k).mono hsub).fun_inv (fun y hy => (hgood y hy.2).2) |>.fun_mul
      ((hGcoeff j).mono hsub)
  · intro y hy hcy
    have hlead := (hgood y hcy).2
    have hQdeg : (Q y).natDegree ≤ k := (natDegree_smul_le _ _).trans (hWsub hy.2)
    have hQcoeff : (Q y).coeff k = 1 := by
      simp only [Q, coeff_smul, smul_eq_mul, inv_mul_cancel₀ hlead]
    refine ⟨monic_of_natDegree_le_of_coeff_eq_one k hQdeg hQcoeff,
      le_antisymm hQdeg (le_natDegree_of_ne_zero (by rw [hQcoeff]; exact one_ne_zero)), ?_⟩
    intro z
    change (∀ i, (P i y).eval z = 0) ↔ (((G y).coeff k)⁻¹ • G y).eval z = 0
    rw [eval_smul, smul_eq_mul, mul_eq_zero, or_iff_right (inv_ne_zero hlead)]
    exact hroot y hy.1 (hgood y hcy).1 z

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericDegree.Constructions.GenericPolynomial
