import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ExtendedIdealCoefficients
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Extended Ideal Tensor Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExtendedIdealTensorCoefficients

noncomputable section

/-! Tensors with an extended ideal use only finitely many coefficients
of the ambient algebra. -/

open TensorProduct

universe u v w
variable {B : Type u} [CommRing B] {A : Type v} [CommRing A] [Algebra B A]

def extendedIdealInclusion (D : Subalgebra B A) (I : Ideal B) :
    I.map (algebraMap B D) →ₗ[B] I.map (algebraMap B A) where
  toFun r := ⟨D.val r.val, by
    have h : D.val.toRingHom.comp (algebraMap B D) = algebraMap B A :=
      RingHom.ext (fun b => D.val.commutes b)
    simpa only [Ideal.map_map, h] using! Ideal.mem_map_of_mem D.val.toRingHom r.property⟩
  map_add' r s := Subtype.ext (D.val.map_add r.val s.val)
  map_smul' b r := Subtype.ext (D.val.toLinearMap.map_smul b r.val)

theorem extendedIdealInclusion_injective (D : Subalgebra B A) (I : Ideal B) :
    Function.Injective (extendedIdealInclusion D I) := by
  intro x y h
  have hh : D.val x.val = D.val y.val :=
    congrArg (fun r : I.map (algebraMap B A) => r.val) h
  exact Subtype.ext (Subtype.val_injective hh)

theorem extendedIdealInclusion_coefficient (D : Subalgebra B A) (I : Ideal B) :
    (extendedIdealInclusion D I).comp (IdealTensor.BaseChange.idealCoefficientInclusion B D I) =
      IdealTensor.BaseChange.idealCoefficientInclusion B A I := by
  ext r
  exact D.val.commutes r.val

variable (C : Subalgebra B A) [Algebra.FiniteType B C]
variable {M : Type w} [AddCommGroup M] [Module B M]

theorem extendedIdealTensor_finite_coefficient_representation (I : Ideal B)
    (z : M ⊗[B] I.map (algebraMap B A)) :
    ∃ D : Subalgebra B A, C ≤ D ∧ Algebra.FiniteType B D ∧
      ∃ w : M ⊗[B] I.map (algebraMap B D), (extendedIdealInclusion D I).lTensor M w = z := by
  classical
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset z
  obtain ⟨D, hCD, hD, hv⟩ := Finite.ExtendedIdealCoefficients.finite_extended_ideal_coefficients C I (fun p : s => p.val.2)
  choose v hv using hv
  refine ⟨D, hCD, hD, ∑ p : s, p.val.1 ⊗ₜ[B] v p, ?_⟩
  have he (p : s) : extendedIdealInclusion D I (v p) = p.val.2 := Subtype.ext (hv p)
  simp only [map_sum, LinearMap.lTensor_tmul, he]
  rw [Finset.univ_eq_attach, Finset.sum_attach s
    (fun p : M × I.map (algebraMap B A) => p.1 ⊗ₜ[B] p.2)]
  exact hs.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExtendedIdealTensorCoefficients
