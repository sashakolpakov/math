import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Algebra.Ring.Idempotent

/-! # Domain From Generic Fiber -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.DomainFromGenericFiber

noncomputable section

/-!
# A local ring detected as a domain by its reduced Artinian extension

An injective map reflects idempotence. If every idempotent of the target comes
from a local source, all target idempotents are trivial. The finite product of
fields classification of reduced Artinian rings then shows that the target is
a field, and hence that the source is a domain.
-/

universe u v

/-- An idempotent in a commutative local ring is zero or one. -/
theorem idempotent_eq_zero_or_one_of_local
    {A : Type u} [CommRing A] [IsLocalRing A] {a : A}
    (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha)
  · left
    have h := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha.one_sub
    exact sub_eq_self.mp h

/-- A nontrivial reduced Artinian commutative ring with no nontrivial
idempotents is a field. -/
theorem isField_of_artinian_reduced_idempotents_trivial
    (B : Type v) [CommRing B] [IsArtinianRing B] [IsReduced B] [Nontrivial B]
    (htriv : ∀ b : B, IsIdempotentElem b → b = 0 ∨ b = 1) : IsField B := by
  classical
  have : Subsingleton (MaximalSpectrum B) := by
    constructor
    intro m n
    let e : ∀ j : MaximalSpectrum B, B ⧸ j.asIdeal :=
      fun j => if j = m then 1 else 0
    have he : IsIdempotentElem e := by
      funext j
      by_cases hj : j = m <;> simp [e, hj]
    have heB : IsIdempotentElem ((IsArtinianRing.equivPi B).symm e) :=
      he.map (IsArtinianRing.equivPi B).symm
    rcases htriv _ heB with hz | ho
    · have h := congrArg (IsArtinianRing.equivPi B) hz
      rw [AlgEquiv.apply_symm_apply, map_zero] at h
      have hm := congrFun h m
      have h10 : (1 : B ⧸ m.asIdeal) = 0 := by
        simpa only [e, ite_eq_left rfl, Pi.zero_apply] using hm
      exact (one_ne_zero h10).elim
    · by_contra hmn
      have h := congrArg (IsArtinianRing.equivPi B) ho
      rw [AlgEquiv.apply_symm_apply, map_one] at h
      have hn := congrFun h n
      have h01 : (0 : B ⧸ n.asIdeal) = 1 := by
        simpa only [e, ite_eq_right (Ne.symm hmn), Pi.one_apply] using hn
      exact zero_ne_one h01
  let : IsLocalRing B := IsLocalRing.of_singleton_maximalSpectrum
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing B

/-- A local ring which embeds in a reduced Artinian ring and lifts all of its
idempotents is a domain. Idempotence of the lifts follows from injectivity, so
it is not an additional assumption. -/
theorem isDomain_of_local_of_artinian_reduced_extension
    {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsArtinianRing B] [IsReduced B]
    (f : A →+* B) (hf : Function.Injective f)
    (hlift : ∀ b : B, IsIdempotentElem b → ∃ a : A, f a = b) : IsDomain A := by
  let : Nontrivial B := hf.nontrivial
  have htriv : ∀ b : B, IsIdempotentElem b → b = 0 ∨ b = 1 := by
    intro b hb
    obtain ⟨a, ha⟩ := hlift b hb
    have haidem : IsIdempotentElem a := by
      change a * a = a
      apply hf
      rw [map_mul, ha]
      exact hb
    rcases idempotent_eq_zero_or_one_of_local haidem with h0 | h1
    · left
      rw [← ha, h0, map_zero]
    · right
      rw [← ha, h1, map_one]
  let : IsDomain B := (isField_of_artinian_reduced_idempotents_trivial B htriv).isDomain
  exact hf.isDomain f

end

end OAI.AlgebraicGeometry.Foundations.Scheme.DomainFromGenericFiber
