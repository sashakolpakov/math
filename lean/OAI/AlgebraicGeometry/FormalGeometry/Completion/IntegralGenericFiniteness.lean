import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralFiniteEmbedding
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FractionBaseChangeDomain
import Mathlib.RingTheory.Unramified.Field

/-! # Integral Generic Finiteness -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralGenericFiniteness.Construction

noncomputable section

/-!
# Completion: generic finiteness implies finiteness for the integral unramified domain

The generic tensor algebra is a finite separable field. Injecting the
actual integral algebra into it permits the trace finiteness argument.
-/

open scoped TensorProduct

universe u v w

variable (R : Type u) (K : Type v) (T : Type w)
  [CommRing R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing T] [IsDomain T] [Algebra R T] [FaithfulSMul R T]
  [Algebra.IsIntegral R T] [Algebra.FormallyUnramified R T]
  [Module.Finite K (K ⊗[R] T)]

include K

/-- A generically finite integral unramified domain over a normal Noetherian ring is finite. -/
theorem integral_unramified_finite_of_generic_finite : Module.Finite R T := by
  have : IsDomain R := Function.Injective.isDomain (algebraMap R T)
    (FaithfulSMul.algebraMap_injective R T)
  let L := K ⊗[R] T
  have : IsDomain L := FractionBaseChangeDomain.Construction.fraction_tensor_isDomain R K T
  have hf : IsField L := isField_of_isIntegral_of_isField' (Field.toIsField K)
  let := hf.toField
  have : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  exact IntegralFiniteEmbedding.Construction.integral_algebra_finite_of_separable_field_embedding R K L T
    Algebra.TensorProduct.includeRight (FractionBaseChangeDomain.Construction.fraction_tensor_includeRight_injective R K T)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralGenericFiniteness.Construction
