import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Principal
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatIntersectionPrincipal
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Factorial -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Factorial.Construction.FactorialDescent

noncomputable section

/-!
# Factoriality descends from a faithfully flat local domain

Flatness preserves intersections of principal ideals. Each such intersection
is principal after extension to a factorial ring; descent of its generator
then constructs least common multiples in the original Noetherian domain.
-/

variable {R S : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [CommRing S] [IsDomain S] [IsLocalRing S] [Algebra R S]

theorem of_faithfullyFlat [Module.FaithfullyFlat R S] [UniqueFactorizationMonoid S] :
    UniqueFactorizationMonoid R := by
  classical
  let := UniqueFactorizationMonoid.toGCDMonoid S
  have hp (a b : R) : (Ideal.span {a} ⊓ Ideal.span {b}).IsPrincipal := by
    apply Principal.Construction.PrincipalDescent.isPrincipal (S := S)
    rw [FlatIntersectionPrincipal.Construction.FlatIntersection.principal]
    refine ⟨GCDMonoid.lcm (algebraMap R S a) (algebraMap R S b), ?_⟩
    ext x
    simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]
  let := gcdMonoidOfExistsLCM fun a b : R => by
    obtain ⟨c, hc⟩ := hp a b
    change Ideal.span {a} ⊓ Ideal.span {b} = Ideal.span {c} at hc
    refine ⟨c, fun d => ?_⟩
    simpa only [Ideal.mem_inf, Ideal.mem_span_singleton] using
      (SetLike.ext_iff.mp hc d)
  infer_instance

theorem of_completion [IsLocalRing R]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal R) R)]
    [UniqueFactorizationMonoid (AdicCompletion (IsLocalRing.maximalIdeal R) R)] :
    UniqueFactorizationMonoid R := by
  let S := AdicCompletion (IsLocalRing.maximalIdeal R) R
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact of_faithfullyFlat (S := S)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Factorial.Construction.FactorialDescent
