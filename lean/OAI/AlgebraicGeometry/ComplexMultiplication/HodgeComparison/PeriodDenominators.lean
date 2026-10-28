import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.LocallyConstant.Basic

/-! # Period Denominators -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodDenominators.CM.Construction

noncomputable section

/-! Finitely many rational transition periods lie in a single rescaling
of the integer span of a rational basis. Compactness makes locally
constant transition functions satisfy this finite condition. -/

variable {U ι : Type*} [AddCommGroup U] [Module ℚ U] [Finite ι]

theorem finite_rational_periods_integer_multiple (b : Module.Basis ι ℚ U)
    (S : Set U) (hS : S.Finite) :
    ∃ d : ℤ, 0 < d ∧ ∀ x ∈ S, d • x ∈ Submodule.span ℤ (Set.range b) := by
  let : Finite S := hS.to_subtype
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun ix : ι × S => b.repr ix.2.val ix.1)
  have hd0 : (d : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  refine ⟨(d : ℤ) ^ 2, sq_pos_of_ne_zero hd0, ?_⟩
  intro x hx
  apply (b.mem_span_iff_repr_mem ℤ _).mpr
  intro i
  have hi := IsLocalization.isInteger_smul (a := (d : ℤ)) (hd (i, ⟨x, hx⟩))
  change ∃ z : ℤ, algebraMap ℤ ℚ z = (d : ℤ) • ((d : ℤ) • b.repr x i) at hi
  obtain ⟨z, hz⟩ := hi
  refine ⟨z, ?_⟩
  simpa only [map_zsmul, Finsupp.smul_apply, pow_two, mul_smul] using hz

theorem compact_locally_constant_periods_integer_multiple {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (b : Module.Basis ι ℚ U)
    (f : X → U) (hf : IsLocallyConstant f) :
    ∃ d : ℤ, 0 < d ∧ ∀ x, d • f x ∈ Submodule.span ℤ (Set.range b) := by
  obtain ⟨d, hd, h⟩ := finite_rational_periods_integer_multiple b (Set.range f) hf.range_finite
  exact ⟨d, hd, fun x => h (f x) ⟨x, rfl⟩⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodDenominators.CM.Construction
