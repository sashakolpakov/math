import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Etale Algebra Reduced -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleAlgebraReduced

noncomputable section

/-! A finite etale algebra over an arbitrary reduced ring is reduced.
Projective-module duals detect elements, and every residue fiber is reduced. -/

open scoped TensorProduct

theorem finite_etale_algebra_isReduced (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] [IsReduced R] [Module.Finite R A] [Algebra.Etale R A] : IsReduced A := by
  have : Module.FinitePresentation R A := Module.FinitePresentation.of_finite_of_finitePresentation R A
  have : Module.Projective R A := Module.Flat.projective_of_finitePresentation
  constructor
  intro a ha
  apply (Module.forall_dual_apply_eq_zero_iff R a).mp
  intro φ
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro p hp
  have : p.IsPrime := hp
  let k := p.ResidueField
  have : IsReduced (k ⊗[R] A) := Algebra.FormallyUnramified.isReduced_of_field k (k ⊗[R] A)
  have hz : (1 : k) ⊗ₜ[R] a = 0 :=
    (ha.map (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := A)).toRingHom).eq_zero
  have hφ := congrArg (fun z : k ⊗[R] A => (TensorProduct.rid R k) ((φ.lTensor k) z)) hz
  apply Ideal.algebraMap_residueField_eq_zero.mp
  simpa only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_zero, Algebra.smul_def,
    mul_one] using hφ

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleAlgebraReduced
