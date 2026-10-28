import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PrimePowerRelations
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

/-! # Level Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReduction

noncomputable section

/-! Canonical reduction of original crystalline objects to a bounded level, with its actual quotient and factorization property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {δ : DividedPowers (Ideal.span {(p : B)})}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (n : ℕ)
  (U : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f)

abbrev object : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f :=
  RelationQuotient.object U {(p : U.ring) ^ (n + 1)}
    (PrimePowerRelations.relation_subset U n)

def hom : object n U ⟶ U :=
  RelationQuotient.hom U {(p : U.ring) ^ (n + 1)}
    (PrimePowerRelations.relation_subset U n)

theorem hom_surjective : Function.Surjective (hom n U).ringMap := Ideal.Quotient.mk_surjective

theorem hom_kernel : RingHom.ker (hom n U).ringMap.toRingHom = (Ideal.span {(p : U.ring)}) ^ (n + 1) :=
  (Ideal.mk_ker).trans (PrimePowerRelations.relationIdeal_eq U n)

theorem prime_power_zero : (p : (object n U).ring) ^ (n + 1) = 0 := by
  have h : (p : U.ring) ^ (n + 1) ∈ RingHom.ker (hom n U).ringMap.toRingHom := by
    rw [hom_kernel]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : U.ring))) (n + 1)
  change (hom n U).ringMap.toRingHom ((p : U.ring) ^ (n + 1)) = 0 at h
  simpa only [map_pow, map_natCast] using h

def boundedObject : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : B)}) (δ := δ) f n :=
  ⟨object n U, prime_power_zero n U⟩

variable {U} {V : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f}
  (α : V ⟶ U) (hV : (p : V.ring) ^ (n + 1) = 0)

include hV in
theorem kills : ∀ x ∈ ({(p : U.ring) ^ (n + 1)} : Set U.ring), α.ringMap x = 0 := by
  rintro x (rfl : x = _)
  change α.ringMap.toRingHom ((p : U.ring) ^ (n + 1)) = 0
  rw [map_pow, map_natCast]
  exact hV

def factor : V ⟶ object n U :=
  RelationLift.liftHom {(p : U.ring) ^ (n + 1)}
    (PrimePowerRelations.relation_subset U n) α (kills n α hV)

theorem factor_comp : factor n α hV ≫ hom n U = α :=
  RelationLift.liftHom_comp {(p : U.ring) ^ (n + 1)}
    (PrimePowerRelations.relation_subset U n) α (kills n α hV)

theorem factor_unique (β : V ⟶ object n U) (hβ : β ≫ hom n U = α) : β = factor n α hV :=
  RelationLift.liftHom_unique {(p : U.ring) ^ (n + 1)}
    (PrimePowerRelations.relation_subset U n) α (kills n α hV) β hβ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReduction
