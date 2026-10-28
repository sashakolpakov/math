import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.BaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoefficientExtension
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Extended Ideal Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ExtendedIdealCoefficients

noncomputable section

/-! Finitely many elements of an extended ideal already come from
one finite intermediate coefficient algebra. -/

open TensorProduct

universe u v w
variable {B : Type u} [CommRing B] {A : Type v} [CommRing A] [Algebra B A]
variable (C : Subalgebra B A) [Algebra.FiniteType B C]
variable (I : Ideal B) {κ : Type w} [Fintype κ]

theorem finite_extended_ideal_coefficients (y : κ → I.map (algebraMap B A)) :
    ∃ D : Subalgebra B A, C ≤ D ∧ Algebra.FiniteType B D ∧
      ∀ i, ∃ z : I.map (algebraMap B D), D.val z.val = (y i).val := by
  classical
  have hr : Set.range (fun r : I => algebraMap B A r.val) = (algebraMap B A) '' (I : Set B) := by
    ext a
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.val, r.property, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  have hc (i : κ) : ∃ c : I →₀ A, (c.sum fun r a => a • algebraMap B A r.val) = (y i).val := by
    apply Finsupp.mem_span_range_iff_exists_finsupp.mp
    rw [hr]
    exact (y i).property
  choose c hc using hc
  let J := Σ i : κ, (c i).support
  let v : J → A := fun p => c p.1 p.2.val
  let D := CoefficientExtension.finiteCoefficientExtension C v
  let d (i : κ) (r : (c i).support) : D :=
    ⟨c i r.val, CoefficientExtension.mem_finiteCoefficientExtension C v ⟨i, r⟩⟩
  let z (i : κ) : D := ∑ r : (c i).support, d i r * algebraMap B D r.val.val
  refine ⟨D, CoefficientExtension.le_finiteCoefficientExtension C v, inferInstance, fun i => ?_⟩
  have hz : z i ∈ I.map (algebraMap B D) := by
    apply Submodule.sum_mem
    intro r _
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ r.val.property)
  refine ⟨⟨z i, hz⟩, ?_⟩
  change D.val (∑ r : (c i).support, d i r * algebraMap B D r.val.val) = (y i).val
  simp only [map_sum, map_mul, AlgHom.commutes]
  change ∑ r : (c i).support, c i r.val * algebraMap B A r.val.val = (y i).val
  rw [Finset.univ_eq_attach, Finset.sum_attach (c i).support
    (fun r : I => c i r * algebraMap B A r.val)]
  simpa only [Finsupp.sum, smul_eq_mul] using hc i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ExtendedIdealCoefficients
