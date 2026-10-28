import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Complex.Basic

/-! # Invariant Differential -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.InvariantDifferential

noncomputable section

/-! The differential of an analytic group law in its last variable is
holomorphic. Near an invertible value its inverse is holomorphic as well. -/

open Set Filter
open scoped _root_.Topology ContDiff Classical

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffOn_multiplication_differential
    (m : P × (V × V) → V) (U : Set (P × (V × V)))
    (hU : IsOpen U) (hm : ContDiffOn ℂ 3 m U) :
    ContDiffOn ℂ 2 (fun q : P × V => fderiv ℂ (fun y => m (q.1, (q.2, y))) 0)
      {q | (q.1, (q.2, (0 : V))) ∈ U} := by
  intro q hq
  let f : (P × V) → V → V := fun z y => m (z.1, (z.2, y))
  have hcoord : ContDiffAt ℂ 3 (fun z : (P × V) × V => (z.1.1, (z.1.2, z.2))) (q, 0) := by
    fun_prop
  have hf : ContDiffAt ℂ 3 (Function.uncurry f) (q, 0) :=
    (hm.contDiffAt (hU.mem_nhds hq)).comp (q, 0) hcoord
  exact (hf.fderiv (g := fun _ => (0 : V)) contDiffAt_const
    (by norm_num : (2 : ℕ∞ω) + 1 ≤ 3)).contDiffWithinAt

theorem exists_holomorphic_inverse_differential_neighborhood [CompleteSpace V]
    (B : P → V →L[ℂ] V) (U : Set P) (hU : IsOpen U) (hB : ContDiffOn ℂ 2 B U)
    (p₀ : P) (hp₀ : p₀ ∈ U) (e₀ : V ≃L[ℂ] V)
    (hcenter : B p₀ = e₀.toContinuousLinearMap) :
    ∃ (W : Set P) (D : P → V ≃L[ℂ] V), IsOpen W ∧ p₀ ∈ W ∧ W ⊆ U ∧
      (∀ p ∈ W, (D p).toContinuousLinearMap = B p) ∧
      ContDiffOn ℂ 2 (fun p => (D p).symm.toContinuousLinearMap) W := by
  have hmem : B ⁻¹' range (fun e : V ≃L[ℂ] V => e.toContinuousLinearMap) ∈ 𝓝 p₀ := by
    apply (hB.continuousOn.continuousAt (hU.mem_nhds hp₀)).preimage_mem_nhds
    rw [hcenter]
    exact e₀.nhds
  obtain ⟨W₀, hsub, hW₀, hpW₀⟩ := mem_nhds_iff.mp hmem
  let W := U ∩ W₀
  have hW : IsOpen W := hU.inter hW₀
  have hchoice (p : P) : ∃ D : V ≃L[ℂ] V, p ∈ W → D.toContinuousLinearMap = B p := by
    by_cases hp : p ∈ W
    · obtain ⟨D, hD⟩ := hsub hp.2
      exact ⟨D, fun _ => hD⟩
    · exact ⟨e₀, fun h => (hp h).elim⟩
  choose D he using hchoice
  have hI : ContDiffOn ℂ 2 (fun p => (B p).inverse) W := by
    intro p hp
    have hInv : ContDiffAt ℂ 2 ContinuousLinearMap.inverse (B p) := by
      rw [← he p hp]
      exact contDiffAt_map_inverse (D p)
    exact hInv.comp_contDiffWithinAt p ((hB.mono inter_subset_left) p hp)
  refine ⟨W, D, hW, ⟨hp₀, hpW₀⟩, inter_subset_left, he, hI.congr ?_⟩
  intro p hp
  rw [← he p hp, ContinuousLinearMap.inverse_equiv]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.InvariantDifferential
