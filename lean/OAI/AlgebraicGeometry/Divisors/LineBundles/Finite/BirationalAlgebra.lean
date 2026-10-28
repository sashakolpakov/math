import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationDivisor

/-! # Birational Algebra -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.BirationalAlgebra.BundleCycles

noncomputable section

/-!
# LineBundleCycles: a finite subalgebra of a normal domain's fraction field is the domain
-/

theorem finiteSubalgebra_algebraMap_bijective
    (A B K : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra A B] [Module.Finite A B]
    (j : B →ₐ[A] K) (hj : Function.Injective j) :
    Function.Bijective (algebraMap A B) := by
  constructor
  · intro a b hab
    apply IsFractionRing.injective A K
    simpa only [AlgHom.commutes] using congrArg j hab
  · intro b
    have hb : IsIntegral A (j b) := (Algebra.IsIntegral.isIntegral b).map j
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hb
    exact ⟨a, hj ((j.commutes a).trans ha)⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.BirationalAlgebra.BundleCycles
