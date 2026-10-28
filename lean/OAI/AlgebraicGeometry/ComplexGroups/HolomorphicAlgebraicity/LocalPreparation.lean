import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.WeierstrassPreparation
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Local Preparation -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LocalPreparation.Constructions.Preparation

noncomputable section

/-!
# Polynomial preparation at a finite analytic fiber

Finiteness of a fiber forces at least one local defining equation to be
nonzero as a one-variable analytic germ. Isolated zeros then provide the
zero-free boundary required by polynomial preparation.
-/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology

theorem exists_nonzero_vertical_equation {n m : ℕ}
    {S W : Set ((Fin n → ℂ) × ℂ)} (hW : IsOpen W) {x : Fin n → ℂ} {c : ℂ}
    (hxc : (x, c) ∈ W) (f : Fin m → ((Fin n → ℂ) × ℂ) → ℂ)
    (heq : ∀ p ∈ W, p ∈ S ↔ ∀ i, f i p = 0)
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite) :
    ∃ i, ¬∀ᶠ z in 𝓝 c, f i (x, z) = 0 := by
  classical
  by_contra h
  have hi : ∀ i, ∀ᶠ z in 𝓝 c, f i (x, z) = 0 := by simpa using h
  have hdomain : ∀ᶠ z in 𝓝 c, (x, z) ∈ W :=
    (hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hxc
  have hfiber : {z : ℂ | (x, z) ∈ S} ∈ 𝓝 c := by
    filter_upwards [hdomain, eventually_all.mpr hi] with z hz hzi
    exact (heq (x, z) hz).mpr hzi
  exact (infinite_of_mem_nhds c hfiber) hfinite

theorem exists_zero_free_circle {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ}
    {W : Set ((Fin n → ℂ) × ℂ)} (hW : IsOpen W) (hF : DifferentiableOn ℂ F W)
    {x : Fin n → ℂ} {c : ℂ} (hxc : (x, c) ∈ W)
    (hn : ¬∀ᶠ z in 𝓝 c, F (x, z) = 0) :
    ∃ R : ℝ, 0 < R ∧ (∀ z ∈ closedBall c R, (x, z) ∈ W) ∧
      ∀ z ∈ sphere c R, F (x, z) ≠ 0 := by
  have ha : AnalyticAt ℂ (fun z => F (x, z)) c :=
    RootFamiliesAt.Constructions.RootFamilies.analyticOnNhd_slice hW hF x (K := {c}) (by simpa using hxc) c (mem_singleton c)
  have hp := eventually_nhdsWithin_iff.mp
    (ha.eventually_eq_zero_or_eventually_ne_zero.resolve_left hn)
  have hdomain : ∀ᶠ z in 𝓝 c, (x, z) ∈ W :=
    (hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hxc
  obtain ⟨R, hR, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hdomain.and hp)
  refine ⟨R, hR, fun z hz => (hball hz).1, fun z hz => ?_⟩
  apply (hball (sphere_subset_closedBall hz)).2
  change z ≠ c
  intro hzc
  have hdist := mem_sphere.mp hz
  rw [hzc, dist_self] at hdist
  exact hR.ne' hdist.symm

/-- A locally analytic set with a finite vertical fiber has, on a product
neighborhood, a monic polynomial constraint with holomorphic coefficients,
together with its original finite family of holomorphic equations. -/
theorem polynomial_constraint_of_finite_fiber {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {x : Fin n → ℂ} {c : ℂ}
    (hlocal : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, c))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite) :
    ∃ (R : ℝ) (d m : ℕ) (U : Set (Fin n → ℂ)) (W : Set ((Fin n → ℂ) × ℂ))
        (P : (Fin n → ℂ) → Polynomial ℂ) (f : Fin m → ((Fin n → ℂ) × ℂ) → ℂ),
      0 < R ∧ IsOpen U ∧ x ∈ U ∧ IsOpen W ∧ U ×ˢ closedBall c R ⊆ W ∧
      (∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U) ∧
      (∀ y ∈ U, (P y).Monic ∧ (P y).natDegree = d ∧
        ∀ z, (P y).eval z = 0 → z ∈ ball c R) ∧
      (∀ i, DifferentiableOn ℂ (f i) W) ∧
      ∀ y ∈ U, ∀ z ∈ closedBall c R,
        (y, z) ∈ S ↔ (P y).eval z = 0 ∧ ∀ i, f i (y, z) = 0 := by
  obtain ⟨W, hW, hxc, m, f, hf, heq⟩ := hlocal
  obtain ⟨i, hi⟩ := exists_nonzero_vertical_equation hW hxc f heq hfinite
  obtain ⟨R, hR, hbase, hn⟩ := exists_zero_free_circle hW (hf i) hxc hi
  obtain ⟨d, U, P, hU, hx, hUW, hcoeff, hP, hPeq⟩ :=
    WeierstrassPreparation.Constructions.Preparation.exists_polynomial_zero_equations hW (hf i) hR hbase hn
  refine ⟨R, d, m, U, W, P, f, hR, hU, hx, hW, hUW, hcoeff, hP, hf, ?_⟩
  intro y hy z hz
  rw [heq (y, z) (hUW ⟨hy, hz⟩)]
  exact ⟨fun h => ⟨(hPeq y hy z hz).mp (h i), h⟩, And.right⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LocalPreparation.Constructions.Preparation
