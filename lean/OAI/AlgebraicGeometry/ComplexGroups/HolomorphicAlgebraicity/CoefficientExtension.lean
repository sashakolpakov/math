import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Quotient
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MonicRoots
import Mathlib.Algebra.Polynomial.OfFn

/-! # Coefficient Extension -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoefficientExtension.Constructions.GenericPolynomial

noncomputable section

section

/-!
# Extending bounded monic polynomial families

Extend the finitely many coefficients across the exceptional zero set and
assemble them into one polynomial family. Density preserves the monic top
coefficient and hence the degree throughout the resulting neighborhood.
-/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology

theorem exists_extended_monic_family {n k : ℕ}
    {P : (Fin n → ℂ) → ℂ[X]} {c : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hc : DifferentiableOn ℂ c U)
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) {y | y ∈ U ∧ c y ≠ 0})
    (hP : ∀ y ∈ U, c y ≠ 0 → (P y).Monic ∧ (P y).natDegree = k)
    (hbound : ∀ j, ∃ M : ℝ, ∀ y ∈ U, c y ≠ 0 → ‖(P y).coeff j‖ ≤ M)
    {x : Fin n → ℂ} (hx : x ∈ U) (hcn : ¬∀ᶠ y in 𝓝 x, c y = 0) :
    ∃ (V : Set (Fin n → ℂ)) (Q : (Fin n → ℂ) → ℂ[X]),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ V ⊆ closure {y | y ∈ V ∧ c y ≠ 0} ∧
      (∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) V) ∧
      (∀ y ∈ V, (Q y).Monic ∧ (Q y).natDegree = k) ∧
      ∀ y ∈ V, c y ≠ 0 → Q y = P y := by
  classical
  have hex (i : Fin (k + 1)) := Quotient.Constructions.Removable.exists_extension_off_zero_set hU hc
    (hcoeff i.val) hx hcn (hbound i.val)
  choose W F hW hxW hWU hF hFeq using hex
  let Z := U ∩ ⋂ i, W i
  have hZ : IsOpen Z := hU.inter (isOpen_iInter_of_finite hW)
  have hxZ : x ∈ Z := ⟨hx, mem_iInter.mpr hxW⟩
  have hZU : Z ⊆ U := inter_subset_left
  obtain ⟨V, hV, hxV, hVZ, hdense⟩ :=
    GenericDegree.Constructions.GenericPolynomial.exists_dense_nonzero_neighborhood hZ hxZ (hc.mono hZU) hcn
  have hVU : V ⊆ U := hVZ.trans hZU
  have hVW (i : Fin (k + 1)) : V ⊆ W i := fun y hy => mem_iInter.mp (hVZ hy).2 i
  let Q : (Fin n → ℂ) → ℂ[X] := fun y => ofFn (k + 1) (fun i => F i y)
  have hQcoeff (j : ℕ) : DifferentiableOn ℂ (fun y => (Q y).coeff j) V := by
    by_cases hj : j < k + 1
    · simp only [Q, ofFn_coeff_eq_val_of_lt _ hj]
      exact (hF ⟨j, hj⟩).mono (hVW ⟨j, hj⟩)
    · simp only [Q, ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hj)]
      exact differentiableOn_const _
  have hQeq (y : Fin n → ℂ) (hy : y ∈ V) (hcy : c y ≠ 0) : Q y = P y := by
    apply Polynomial.ext
    intro j
    by_cases hj : j < k + 1
    · simp only [Q, ofFn_coeff_eq_val_of_lt _ hj]
      exact hFeq ⟨j, hj⟩ y (hVW ⟨j, hj⟩ hy) hcy
    · rw [show (Q y).coeff j = 0 from ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hj)]
      exact (coeff_eq_zero_of_natDegree_lt (by rw [(hP y (hVU hy) hcy).2]; omega)).symm
  have hQtop (y : Fin n → ℂ) (hy : y ∈ V) : (Q y).coeff k = 1 := by
    apply tendsto_nhds_unique_of_frequently_eq
      ((hQcoeff k).differentiableAt (hV.mem_nhds hy)).continuousAt.tendsto tendsto_const_nhds
    apply (mem_closure_iff_frequently.mp (hdense hy)).mono
    intro z hz
    rw [hQeq z hz.1 hz.2, ← (hP z (hVU hz.1) hz.2).2]
    exact (hP z (hVU hz.1) hz.2).1.coeff_natDegree
  refine ⟨V, Q, hV, hxV, hVU, hdense, hQcoeff, ?_, hQeq⟩
  intro y hy
  have hdeg : (Q y).natDegree ≤ k := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one k hdeg (hQtop y hy),
    le_antisymm hdeg (le_natDegree_of_ne_zero (by rw [hQtop y hy]; exact one_ne_zero))⟩

end

/-!
# Uniqueness of extended generic root polynomials

Two holomorphic polynomial families with the same generic distinct roots
agree near the base point. The nonzero locus of the product of their
exceptional functions is dense, and continuity identifies all coefficients.
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

theorem eventually_eq_of_generic_roots {n : ℕ}
    {P Q : (Fin n → ℂ) → ℂ[X]} {c d : (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) {x : Fin n → ℂ} (hx : x ∈ U)
    (hc : DifferentiableOn ℂ c U) (hd : DifferentiableOn ℂ d U)
    (hcn : ¬∀ᶠ y in 𝓝 x, c y = 0) (hdn : ¬∀ᶠ y in 𝓝 x, d y = 0)
    (hP : ∀ j, ContinuousOn (fun y => (P y).coeff j) U)
    (hQ : ∀ j, ContinuousOn (fun y => (Q y).coeff j) U)
    (hroot : ∀ y ∈ U, c y ≠ 0 → d y ≠ 0 →
      (P y).Monic ∧ (Q y).Monic ∧ (P y).Separable ∧ (Q y).Separable ∧
        ∀ z : ℂ, (P y).eval z = 0 ↔ (Q y).eval z = 0) :
    P =ᶠ[𝓝 x] Q := by
  have hprod := GenericDegree.Constructions.GenericPolynomial.not_eventually_zero_mul hU hx hc hd hcn hdn
  obtain ⟨V, hV, hxV, hVU, hdense⟩ :=
    GenericDegree.Constructions.GenericPolynomial.exists_dense_nonzero_neighborhood hU hx (hc.fun_mul hd) hprod
  filter_upwards [hV.mem_nhds hxV] with y hy
  apply Polynomial.ext
  intro j
  apply tendsto_nhds_unique_of_frequently_eq
    ((hP j).continuousAt (hU.mem_nhds (hVU hy))).tendsto
    ((hQ j).continuousAt (hU.mem_nhds (hVU hy))).tendsto
  apply (mem_closure_iff_frequently.mp (hdense hy)).mono
  intro z hz
  obtain ⟨hcz, hdz⟩ := mul_ne_zero_iff.mp hz.2
  obtain ⟨hPm, hQm, hPs, hQs, hr⟩ := hroot z (hVU hz.1) hcz hdz
  exact congrArg (fun R : ℂ[X] => R.coeff j) (MonicRoots.Constructions.RootPolynomials.eq_of_same_roots hPm hQm hPs hQs hr)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoefficientExtension.Constructions.GenericPolynomial
