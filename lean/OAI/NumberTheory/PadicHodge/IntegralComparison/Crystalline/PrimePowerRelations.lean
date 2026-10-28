import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelationLift
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation

/-! # Prime Power Relations -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PrimePowerRelations

noncomputable section

/-! In an original crystalline object, the prime-power relation generates exactly the ordinary prime-power ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {δ : DividedPowers (Ideal.span {(p : B)})}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  (U : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f) (n : ℕ)

theorem mapped_power : ((Ideal.span {(p : B)}) ^ (n + 1)).map U.base =
    (Ideal.span {(p : U.ring)}) ^ (n + 1) := by
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]

theorem stable : DividedPowers.IsSubDPIdeal U.dividedPowers ((Ideal.span {(p : U.ring)}) ^ (n + 1)) := by
  rw [← mapped_power U n]
  exact DividedPowers.isSubDPIdeal_map_of_isSubDPIdeal U.baseCompatible
    (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.power_isSubDPIdeal B (Ideal.span {(p : B)}) δ n)

theorem relation_subset : ({(p : U.ring) ^ (n + 1)} : Set U.ring) ⊆ U.ideal := by
  rintro a (rfl : a = _)
  exact (stable U n).isSubideal
    (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : U.ring))) (n + 1))

theorem relationIdeal_eq : DividedPower.Relations.relationIdeal U.dividedPowers {(p : U.ring) ^ (n + 1)} =
    (Ideal.span {(p : U.ring)}) ^ (n + 1) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨m, hm, x, hx, rfl⟩
    rcases hx with rfl
    exact (stable U n).dpow_mem m hm
      (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : U.ring))) (n + 1))
  · rw [Ideal.span_singleton_pow]
    apply Ideal.span_le.mpr
    intro a ha
    exact DividedPower.Relations.relation_mem U.dividedPowers {(p : U.ring) ^ (n + 1)}
      (relation_subset U n) ha

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PrimePowerRelations
