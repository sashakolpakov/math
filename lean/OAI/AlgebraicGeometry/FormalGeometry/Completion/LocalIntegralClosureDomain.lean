import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralIdempotents
import Mathlib.RingTheory.Artinian.Ring

/-! # Local Integral Closure Domain -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.LocalIntegralClosureDomain.Construction

noncomputable section

/-!
# Completion: local rings integrally closed in reduced Artinian algebras

The finite product-of-fields decomposition cannot have multiple factors:
its idempotents would give nontrivial idempotents in the local ring. The
ambient algebra is therefore a field, and the local ring is a domain.
-/

universe u v

/-- A nontrivial reduced Artinian ring with no nontrivial idempotents is a field. -/
theorem reduced_artinian_isField_of_idempotents (B : Type v) [CommRing B]
    [Nontrivial B] [IsReduced B] [IsArtinianRing B]
    (h : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : IsField B := by
  classical
  let e := IsArtinianRing.equivPi B
  have : Subsingleton (MaximalSpectrum B) := ⟨fun i j => by
    by_contra hij
    let v : ∀ m : MaximalSpectrum B, B ⧸ m.asIdeal := Pi.single i 1
    have hv : IsIdempotentElem v := by
      change v * v = v
      ext m
      by_cases hm : m = i
      · subst m
        simp [v]
      · simp [v, Pi.single_eq_of_ne hm]
    have ht : IsIdempotentElem (e.symm v) := hv.map e.symm
    rcases h (e.symm v) ht with ht | ht
    · have hh := congrArg (fun b : B => e b i) ht
      simp [v] at hh
    · have hh := congrArg (fun b : B => e b j) ht
      simp [v, Pi.single_eq_of_ne (Ne.symm hij)] at hh⟩
  have : IsLocalRing B := IsLocalRing.of_singleton_maximalSpectrum
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing B

/-- A local ring integrally closed in a reduced Artinian algebra is a domain. -/
theorem local_integrallyClosedIn_artinian_isDomain (R : Type u) (B : Type v)
    [CommRing R] [CommRing B] [Algebra R B] [IsLocalRing R]
    [IsIntegrallyClosedIn R B] [IsReduced B] [IsArtinianRing B] : IsDomain R := by
  have hi := IsIntegralClosure.algebraMap_injective R R B
  have : Nontrivial B := Function.Injective.nontrivial hi
  have hf : IsField B := reduced_artinian_isField_of_idempotents B
    (fun _ he => IntegralIdempotents.Construction.integralClosure_local_idempotent_eq_zero_or_one R he)
  let := hf.toField
  exact Function.Injective.isDomain (algebraMap R B) hi

/-- The same local ring is integrally closed in its own fraction field. -/
theorem local_integrallyClosedIn_artinian_isIntegrallyClosed (R : Type u) (B : Type v)
    [CommRing R] [CommRing B] [Algebra R B] [IsLocalRing R]
    [IsIntegrallyClosedIn R B] [IsReduced B] [IsArtinianRing B] : IsIntegrallyClosed R := by
  have hi := IsIntegralClosure.algebraMap_injective R R B
  have : Nontrivial B := Function.Injective.nontrivial hi
  have hf : IsField B := reduced_artinian_isField_of_idempotents B
    (fun _ he => IntegralIdempotents.Construction.integralClosure_local_idempotent_eq_zero_or_one R he)
  let := hf.toField
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hi
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn R B

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.LocalIntegralClosureDomain.Construction
