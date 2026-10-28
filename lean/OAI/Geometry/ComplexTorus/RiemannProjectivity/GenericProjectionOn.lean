import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicRegularityAt
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Generic Projection On -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.GenericProjectionOn.Constructions.GenericProjection

noncomputable section

/-!
# RiemannProjectivity: projections avoiding a parametrized projective cone

Matrices killing a normalized projective vector have one column determined
by the others. Their incidence parametrization has smaller real dimension
than the full matrix space when the target dimension exceeds the dimension
of the projective parameter space. Hausdorff dimension supplies a matrix
outside every bad incidence image.
-/

open Set Filter _root_.Metric _root_.Module
open scoped _root_.Topology BigOperators ENNReal

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

/-- Holomorphic images of open sets have at most the real dimension of their domain. -/
theorem dimH_image_le_of_holomorphic {U : Set V} {f : V → W}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    dimH (f '' U) ≤ finrank ℝ V := by
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  let : SecondCountableTopology V := inferInstance
  let : CompleteSpace W := FiniteDimensional.complete ℂ W
  apply le_trans (dimH_image_le_of_locally_lipschitzOn ?_)
    ((dimH_mono (subset_univ U)).trans_eq (Real.dimH_univ_eq_finrank V))
  intro x hx
  obtain ⟨C, D, hD, hL⟩ :=
    (HolomorphicRegularityAt.Constructions.HolomorphicRegularity.contDiffAt_one_of_differentiableOn hU hf hx).exists_lipschitzOnWith
  exact ⟨C, D, mem_nhdsWithin_of_mem_nhds hD, hL⟩

variable {n k : ℕ}

/-- Insert the unique column forced by annihilating a normalized vector. -/
def badMatrix (i : Fin (n + 1)) (r : V → Fin n → ℂ)
    (p : V × (Fin n → Fin k → ℂ)) : Fin (n + 1) → Fin k → ℂ :=
  i.insertNth (-∑ j, r p.1 j • p.2 j) p.2

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V] in
theorem differentiableOn_badMatrix (i : Fin (n + 1)) {U : Set V}
    {r : V → Fin n → ℂ} (hr : DifferentiableOn ℂ r U) :
    DifferentiableOn ℂ (badMatrix (k := k) i r) (U ×ˢ univ) := by
  have hB : DifferentiableOn ℂ (fun p : V × (Fin n → Fin k → ℂ) => p.2)
      (U ×ˢ univ) := differentiable_snd.differentiableOn
  apply differentiableOn_pi.mpr
  intro j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · simp only [badMatrix, Fin.insertNth_apply_same]
    apply DifferentiableOn.neg
    apply DifferentiableOn.fun_sum
    intro l _
    exact ((differentiableOn_pi.mp hr l).comp differentiable_fst.differentiableOn
      (fun p hp => hp.1)).smul
      (differentiableOn_pi.mp hB l)
  · simpa only [badMatrix, Fin.insertNth_apply_succAbove] using
      differentiableOn_pi.mp hB l

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V] in
/-- The incidence parametrization captures every matrix killing a vector in its chart. -/
theorem eq_badMatrix_of_annihilates (i : Fin (n + 1)) (r : V → Fin n → ℂ)
    (z : V) (v : Fin (n + 1) → ℂ) (M : Fin (n + 1) → Fin k → ℂ)
    (hi : v i ≠ 0) (hr : ∀ j, v (i.succAbove j) / v i = r z j)
    (hM : ∑ j, v j • M j = 0) :
    M = badMatrix i r (z, i.removeNth M) := by
  apply Fin.eq_insertNth_iff.mpr
  refine ⟨?_, rfl⟩
  have hsum : v i • M i + ∑ j : Fin n, v (i.succAbove j) • M (i.succAbove j) = 0 := by
    rw [Fin.sum_univ_succAbove _ i] at hM
    exact hM
  have hnorm := congrArg (fun w : Fin k → ℂ => (v i)⁻¹ • w) hsum
  simp only [smul_add, Finset.smul_sum, smul_smul, inv_mul_cancel₀ hi, one_smul,
    smul_zero] at hnorm
  have heq : (∑ j : Fin n, ((v i)⁻¹ * v (i.succAbove j)) • M (i.succAbove j)) =
      ∑ j : Fin n, r z j • i.removeNth M j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← hr j, div_eq_mul_inv, mul_comm]
    rfl
  rw [heq] at hnorm
  exact eq_neg_of_add_eq_zero_left hnorm

/-- Matrices outside all the bad projective incidence images are dense. -/
theorem dense_matrices_avoiding (hk : finrank ℂ V < k)
    (U : Fin (n + 1) → Set V) (r : Fin (n + 1) → V → Fin n → ℂ)
    (hU : ∀ i, IsOpen (U i)) (hr : ∀ i, DifferentiableOn ℂ (r i) (U i)) :
    Dense {M : Fin (n + 1) → Fin k → ℂ |
      ∀ i z, z ∈ U i → ∀ B, M ≠ badMatrix i (r i) (z, B)} := by
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  let B : Set (Fin (n + 1) → Fin k → ℂ) :=
    ⋃ i, badMatrix i (r i) '' (U i ×ˢ univ)
  have hdim : dimH B ≤ (finrank ℝ (V × (Fin n → Fin k → ℂ)) : ℝ≥0∞) := by
    rw [show B = _ from rfl, dimH_iUnion]
    exact iSup_le fun i => dimH_image_le_of_holomorphic
      ((hU i).prod isOpen_univ) (differentiableOn_badMatrix i (hr i))
  have hlt : finrank ℝ (V × (Fin n → Fin k → ℂ)) <
      finrank ℝ (Fin (n + 1) → Fin k → ℂ) := by
    have hV : finrank ℝ V = 2 * finrank ℂ V := by
      rw [← Module.finrank_mul_finrank ℝ ℂ V, Complex.finrank_real_complex]
    simp only [Module.finrank_prod, Module.finrank_pi_fintype,
      Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hV]
    nlinarith
  apply (dense_compl_of_dimH_lt_finrank
    (hdim.trans_lt (Nat.cast_lt.mpr hlt))).mono
  intro M hM i z hz C heq
  apply hM
  exact mem_iUnion.mpr ⟨i, ⟨(z, C), ⟨hz, mem_univ _⟩, heq.symm⟩⟩

/-- A matrix exists outside all the bad projective incidence images. -/
theorem exists_matrix_avoiding (hk : finrank ℂ V < k)
    (U : Fin (n + 1) → Set V) (r : Fin (n + 1) → V → Fin n → ℂ)
    (hU : ∀ i, IsOpen (U i)) (hr : ∀ i, DifferentiableOn ℂ (r i) (U i)) :
    ∃ M : Fin (n + 1) → Fin k → ℂ,
      ∀ i z, z ∈ U i → ∀ B, M ≠ badMatrix i (r i) (z, B) :=
  (dense_matrices_avoiding hk U r hU hr).nonempty

/-- A linear projection has no nonzero kernel vector on the covered cone. -/
theorem exists_projection_avoiding (hk : finrank ℂ V < k)
    (U : Fin (n + 1) → Set V) (r : Fin (n + 1) → V → Fin n → ℂ)
    (hU : ∀ i, IsOpen (U i)) (hr : ∀ i, DifferentiableOn ℂ (r i) (U i))
    (S : Set (Fin (n + 1) → ℂ))
    (hcover : ∀ v ∈ S, v ≠ 0 → ∃ i z, z ∈ U i ∧ v i ≠ 0 ∧
      ∀ j, v (i.succAbove j) / v i = r i z j) :
    ∃ L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin k → ℂ),
      ∀ v ∈ S, L v = 0 → v = 0 := by
  obtain ⟨M, hM⟩ := exists_matrix_avoiding hk U r hU hr
  let L : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin k → ℂ) :=
    { toFun := fun v => ∑ j, v j • M j
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }
  refine ⟨L.toContinuousLinearMap, fun v hv hLv => ?_⟩
  by_contra hv0
  obtain ⟨i, z, hz, hi, hratio⟩ := hcover v hv hv0
  exact hM i z hz (i.removeNth M) (eq_badMatrix_of_annihilates i (r i) z v M hi hratio hLv)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.GenericProjectionOn.Constructions.GenericProjection
