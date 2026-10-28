import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.PrimeEuler
import Mathlib.RingTheory.KrullDimension.Regular

/-! # Isolated Parameter Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedParameterDimension

noncomputable section

/-! A parameter whose module fiber is supported only at the closed
point forces the module support to have dimension at most one. Thus
every nonclosed support prime is minimal in that support. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (M : ModuleCat.{u} R) [Module.Finite R M] (r : R)
  (hisolated : Module.support R M ∩ Module.support R (R ⧸ Ideal.span {r}) ⊆ {closedPoint R})

include hisolated

omit [IsNoetherianRing R] in
theorem quotient_support : Module.support R (QuotSMulTop r M) ⊆ {closedPoint R} := by
  rw [Module.support_quotSMulTop]
  intro p hp
  apply hisolated
  refine ⟨hp.1, ?_⟩
  rw [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  exact Ideal.span_le.mpr hp.2

theorem dimension (hr : r ∈ maximalIdeal R) : Module.supportDim R M ≤ 1 := by
  have hs := quotient_support R M r hisolated
  let : Subsingleton (Module.support R (QuotSMulTop r M)) := ⟨fun p q =>
    Subtype.ext ((Set.mem_singleton_iff.mp (hs p.property)).trans (Set.mem_singleton_iff.mp (hs q.property)).symm)⟩
  have hd : Module.supportDim R (QuotSMulTop r M) ≤ 0 := Order.krullDim_nonpos_of_subsingleton
  have hsum : Module.supportDim R (QuotSMulTop r M) + 1 ≤ (0 : WithBot ℕ∞) + 1 := add_le_add hd le_rfl
  have h := (Module.supportDim_le_supportDim_quotSMulTop_succ (M := M) hr).trans hsum
  simpa only [zero_add] using h

theorem minimal (hr : r ∈ maximalIdeal R) (p : PrimeSpectrum R) (hp : p ∈ Module.support R M)
    (hne : p ≠ closedPoint R) (q : PrimeSpectrum R) (hq : q ∈ Module.support R M)
    (hqp : q.asIdeal ≤ p.asIdeal) : q = p := by
  have hd : Order.krullDim (Module.support R M) ≤ 1 := dimension R M r hisolated hr
  rcases (Order.krullDim_le_one_iff.mp hd) ⟨p, hp⟩ with hmin | hmax
  · apply PrimeSpectrum.ext
    exact le_antisymm hqp (hmin (b := ⟨q, hq⟩) hqp)
  · have hpm : p.asIdeal ≤ maximalIdeal R := le_maximalIdeal p.isPrime.ne_top
    have hm : closedPoint R ∈ Module.support R M := Module.mem_support_mono hpm hp
    have hmp : (⟨closedPoint R, hm⟩ : Module.support R M) ≤ ⟨p, hp⟩ := hmax hpm
    exact (hne (PrimeSpectrum.ext (le_antisymm hpm hmp))).elim

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedParameterDimension
