import Mathlib.RingTheory.Ideal.GoingUp

/-! # Integral Split Map -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralSplitMap.Construction

/-!
# Completion: split integral maps into a domain

A retraction of an integral extension into a domain is injective, since
its kernel contracts to zero. Thus the extension is an isomorphism.
-/

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  [Nontrivial R] [IsDomain S]

/-- A retraction of an integral ring map into a domain is injective. -/
theorem integral_retraction_injective (f : R →+* S) (g : S →+* R)
    (hf : f.IsIntegral) (h : g.comp f = RingHom.id R) : Function.Injective g := by
  let := f.toAlgebra
  have : Algebra.IsIntegral R S := algebraMap_isIntegral_iff.mp hf
  apply (RingHom.injective_iff_ker_eq_bot g).mpr
  apply Ideal.eq_bot_of_under_eq_bot (R := R)
  change Ideal.comap f (RingHom.ker g) = ⊥
  rw [RingHom.comap_ker, h]
  exact (RingHom.injective_iff_ker_eq_bot (RingHom.id R)).mp Function.injective_id

/-- A split integral extension into a domain is bijective. -/
theorem integral_split_bijective (f : R →+* S) (g : S →+* R)
    (hf : f.IsIntegral) (h : g.comp f = RingHom.id R) : Function.Bijective f := by
  have hg := integral_retraction_injective f g hf h
  have hr (r : R) : g (f r) = r := congrArg (fun k : R →+* R => k r) h
  refine ⟨fun x y hxy => by simpa only [hr] using congrArg g hxy, fun s => ?_⟩
  exact ⟨g s, hg (hr (g s))⟩

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralSplitMap.Construction
