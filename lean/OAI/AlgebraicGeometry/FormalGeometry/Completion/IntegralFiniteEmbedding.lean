import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! # Integral Finite Embedding -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralFiniteEmbedding.Construction

noncomputable section

/-!
# Completion: finiteness of an integral algebra embedded in a finite separable extension

The trace bound makes the integral closure finite over the normal
Noetherian base. An integral algebra embedded in that field is a
submodule of this finite module and is therefore finite as well.
-/

universe u v w z

/-- The trace finiteness theorem applies to any injectively embedded integral algebra. -/
theorem integral_algebra_finite_of_separable_field_embedding
    (R : Type u) (K : Type v) (L : Type w) (S : Type z)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (j : S →ₐ[R] L) (hj : Function.Injective j) : Module.Finite R S := by
  have : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R K L (integralClosure R L)
  let e : S →ₐ[R] integralClosure R L :=
    j.codRestrict _ (fun s => (Algebra.IsIntegral.isIntegral s).map j)
  have he : Function.Injective e := fun _ _ h => hj (congrArg Subtype.val h)
  have : IsNoetherian R S := isNoetherian_of_injective e.toLinearMap he
  exact Module.IsNoetherian.finite R S

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralFiniteEmbedding.Construction
