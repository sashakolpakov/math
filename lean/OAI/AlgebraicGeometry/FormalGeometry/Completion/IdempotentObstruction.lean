import OAI.AlgebraicGeometry.FormalGeometry.Completion.FunctionsComparison
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # Idempotent Obstruction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IdempotentObstruction.Construction

noncomputable section

/-!
# Completion: the actual infinitesimal idempotent obstructs surjectivity of the comparison

For a Noetherian local base the completed base ring is local. Any idempotent
in the image of a ring map from a local ring is trivial. Hence the canonical
idempotent of a separated initial fiber cannot lie in the image of the actual
formal-functions comparison. Surjectivity for the proper normalized family
is still an obligation to prove.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Every idempotent in the image of a ring map from a local ring is zero or one. -/
theorem localRing_image_idempotent_trivial {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] (φ : R →+* S) (a : R) (he : IsIdempotentElem (φ a)) :
    φ a = 0 ∨ φ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit (h.map φ)).mp he)
  · have h' : IsUnit (1 - φ a) := by simpa only [map_sub, map_one] using h.map φ
    exact Or.inl (sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit h').mp he.one_sub))

/-- The actual nontrivial infinitesimal clopen indicator is outside the image of the completed base. -/
theorem infinitesimalClopenIndicator_not_mem_comparison_range
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (U : (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood (IsLocalRing.maximalIdeal R) f 0).Opens)
    (hU : IsClosed (U : Set (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood (IsLocalRing.maximalIdeal R) f 0)))
    (h₀ : U ≠ ⊥) (h₁ : U ≠ ⊤) :
    Infinitesimal.ClopenSections.Construction.infinitesimalClopenIndicator (IsLocalRing.maximalIdeal R) f U hU ∉
      Set.range (FunctionsComparison.Construction.formalFunctionsComparison (IsLocalRing.maximalIdeal R) f) := by
  obtain ⟨he, hz, ho⟩ :=
    Infinitesimal.ClopenSections.Construction.infinitesimalClopenIndicator_nontrivial (IsLocalRing.maximalIdeal R) f U hU h₀ h₁
  rintro ⟨a, ha⟩
  have he' : IsIdempotentElem (FunctionsComparison.Construction.formalFunctionsComparison (IsLocalRing.maximalIdeal R) f a) :=
    ha.symm ▸ he
  rcases localRing_image_idempotent_trivial
    (FunctionsComparison.Construction.formalFunctionsComparison (IsLocalRing.maximalIdeal R) f) a he' with h | h
  · exact hz (ha.symm.trans h)
  · exact ho (ha.symm.trans h)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IdempotentObstruction.Construction
