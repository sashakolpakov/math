import OAI.Geometry.ComplexTorus.RiemannProjectivity.GlueReduced
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Constant Fiber -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ConstantFiber.Constructions.ConstantFiberDegree

noncomputable section

/-! # RiemannProjectivity: the degree of the canonical family is constant on the punctured base -/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem continuousOn_natDegree {Q : V → ℂ[X]} {B : Set V} {S : Set (V × ℂ)}
    (hlocal : ∀ x ∈ B, ∃ U : Set V, IsOpen U ∧ x ∈ U ∧ U ⊆ B ∧ ReducedFamiliesOn.Constructions.ReducedFamilies.On S U Q) :
    ContinuousOn (fun x => (Q x).natDegree) B := by
  intro x hx
  obtain ⟨U, hU, hxU, _, hOn⟩ := hlocal x hx
  obtain ⟨k, hk⟩ := hOn.constant_degree
  have heq : (fun y => (Q y).natDegree) =ᶠ[𝓝 x] (fun _ => k) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact hk y hy
  exact heq.continuousAt.continuousWithinAt

theorem punctured_preconnected (d : ℕ) :
    IsPreconnected ({x | x ≠ 0} : Set (Fin (d + 1) → ℂ)) := by
  have hdim : 1 < Module.finrank ℝ (Fin (d + 1) → ℂ) := by
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hrank : 1 < Module.rank ℝ (Fin (d + 1) → ℂ) := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hdim
  exact (isConnected_compl_singleton_of_one_lt_rank hrank 0).isPreconnected

theorem exists_constant_degree {d : ℕ} {Q : (Fin (d + 1) → ℂ) → ℂ[X]}
    {S : Set ((Fin (d + 1) → ℂ) × ℂ)}
    (hlocal : ∀ x, x ≠ 0 → ∃ U : Set (Fin (d + 1) → ℂ),
      IsOpen U ∧ x ∈ U ∧ U ⊆ {y | y ≠ 0} ∧ ReducedFamiliesOn.Constructions.ReducedFamilies.On S U Q) :
    ∃ k : ℕ, ∀ x, x ≠ 0 → (Q x).natDegree = k := by
  have hc := continuousOn_natDegree hlocal
  have hnonzero : (fun _ : Fin (d + 1) => (1 : ℂ)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 0)
  exact ⟨(Q (fun _ => 1)).natDegree,
    fun x hx => (punctured_preconnected d).constant hc hx hnonzero⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ConstantFiber.Constructions.ConstantFiberDegree
