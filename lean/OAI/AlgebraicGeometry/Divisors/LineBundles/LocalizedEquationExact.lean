import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Localization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.PeriodicComplex
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-! # Localized Equation Exact -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationExact.BundleCycles

noncomputable section

/-!
# LineBundleCycles: local exactness for the actual branch multiplication complex

Localization of multiplication is multiplication by the same scalar.
The constructed equivalence from a localized branch image to the
localized product quotient therefore transfers exactness at its prime.
-/

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

theorem localizedEndomorphism_equation (S : Submonoid R) (a : R) :
    Periodic.Localization.BundleCycles.localizedEndomorphism S (MultiplicationSequence.BundleCycles.equationEndomorphism a M) =
      MultiplicationSequence.BundleCycles.equationEndomorphism a (LocalizedModule S M) := by
  unfold Periodic.Localization.BundleCycles.localizedEndomorphism MultiplicationSequence.BundleCycles.equationEndomorphism
  rw [map_smul, IsLocalizedModule.map_id]

theorem equationEndomorphism_exact_equiv (a b : R) (e : M ≃ₗ[R] N)
    (h : Function.Exact (MultiplicationSequence.BundleCycles.equationEndomorphism a M) (MultiplicationSequence.BundleCycles.equationEndomorphism b M)) :
    Function.Exact (MultiplicationSequence.BundleCycles.equationEndomorphism a N) (MultiplicationSequence.BundleCycles.equationEndomorphism b N) := by
  apply Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := e) (e₂ := e) (e₃ := e) _ _ h
  · apply LinearMap.ext
    intro m
    exact (e.map_smul a m).symm
  · apply LinearMap.ext
    intro m
    exact (e.map_smul b m).symm

theorem equationEndomorphism_localized_exact (S : Submonoid R) (a b : R)
    (h : Function.Exact (MultiplicationSequence.BundleCycles.equationEndomorphism a M) (MultiplicationSequence.BundleCycles.equationEndomorphism b M)) :
    Function.Exact (MultiplicationSequence.BundleCycles.equationEndomorphism a (LocalizedModule S M))
      (MultiplicationSequence.BundleCycles.equationEndomorphism b (LocalizedModule S M)) := by
  have he := LocalizedModule.map_exact S (MultiplicationSequence.BundleCycles.equationEndomorphism a M) (MultiplicationSequence.BundleCycles.equationEndomorphism b M) h
  change Function.Exact (Periodic.Localization.BundleCycles.localizedEndomorphism S (MultiplicationSequence.BundleCycles.equationEndomorphism a M))
    (Periodic.Localization.BundleCycles.localizedEndomorphism S (MultiplicationSequence.BundleCycles.equationEndomorphism b M)) at he
  rw [localizedEndomorphism_equation, localizedEndomorphism_equation] at he
  exact he

variable [IsDomain R]

theorem productBranch_local_exact (a b : R) (hb : b ≠ 0) (P : Ideal R) [P.IsPrime] :
    Function.Exact
      (MultiplicationSequence.BundleCycles.equationEndomorphism a (LocalizedModule P.primeCompl (Branch.PeriodicComplex.BundleCycles.productBranchModule a b P)))
      (MultiplicationSequence.BundleCycles.equationEndomorphism b (LocalizedModule P.primeCompl (Branch.PeriodicComplex.BundleCycles.productBranchModule a b P))) :=
  equationEndomorphism_exact_equiv a b (Branch.PeriodicComplex.BundleCycles.productBranchLocalEquiv a b P).symm
    (equationEndomorphism_localized_exact P.primeCompl a b (ProductPeriodicComplex.BundleCycles.productEquation_exact a b hb))

theorem productBranch_local_exact_reverse (a b : R) (ha : a ≠ 0) (P : Ideal R) [P.IsPrime] :
    Function.Exact
      (MultiplicationSequence.BundleCycles.equationEndomorphism b (LocalizedModule P.primeCompl (Branch.PeriodicComplex.BundleCycles.productBranchModule a b P)))
      (MultiplicationSequence.BundleCycles.equationEndomorphism a (LocalizedModule P.primeCompl (Branch.PeriodicComplex.BundleCycles.productBranchModule a b P))) :=
  equationEndomorphism_exact_equiv b a (Branch.PeriodicComplex.BundleCycles.productBranchLocalEquiv a b P).symm
    (equationEndomorphism_localized_exact P.primeCompl b a (ProductPeriodicComplex.BundleCycles.productEquation_exact_reverse a b ha))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationExact.BundleCycles
