import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PrincipalIsolation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor

/-! # Support Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportEuler

noncomputable section

/-! Native reduced-support Euler characteristics and isolated
pairings transport along an open immersion's actual stalk isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {Y X : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j]
  (A B : IrreducibleCloseds Y) (A' B' : IrreducibleCloseds X)
  (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint A') (hB : j (CycleClass.Thom.IntersectionGeometry.supportPoint B) = CycleClass.Thom.IntersectionGeometry.supportPoint B')
  (y : Y) (hyA : y ∈ (A : Set Y)) (hyB : y ∈ (B : Set Y))
  (hxA : j y ∈ (A' : Set X)) (hxB : j y ∈ (B' : Set X))

include hA hB

theorem euler (d : ℕ) :
    Tor.Euler.euler (Y.presheaf.stalk y) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hyA) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B y hyB) d =
      Tor.Euler.euler (X.presheaf.stalk (j y))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X A' (j y) hxA) (CycleClass.Thom.IntersectionGeometry.localSupportModule X B' (j y) hxB) d := by
  change (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * (CycleClass.Thom.IntersectionGeometry.localTorLength Y A B y hyA hyB i).toNat) =
    ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * (CycleClass.Thom.IntersectionGeometry.localTorLength X A' B' (j y) hxA hxB i).toNat
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ i * (l.toNat : ℚ))
    (SupportTor.localTorLength_eq j A B A' B' hA hB y hyA hyB hxA hxB i)

theorem isolated
    (hi : Module.support (Y.presheaf.stalk y) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hyA) ∩
      Module.support (Y.presheaf.stalk y) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B y hyB) ⊆
        {IsLocalRing.closedPoint (Y.presheaf.stalk y)}) :
    Module.support (X.presheaf.stalk (j y)) (CycleClass.Thom.IntersectionGeometry.localSupportModule X A' (j y) hxA) ∩
      Module.support (X.presheaf.stalk (j y)) (CycleClass.Thom.IntersectionGeometry.localSupportModule X B' (j y) hxB) ⊆
        {IsLocalRing.closedPoint (X.presheaf.stalk (j y))} := by
  rw [PrincipalIsolation.support j A A' hA y hyA hxA,
    PrincipalIsolation.support j B B' hB y hyB hxB] at hi
  intro p hp
  obtain ⟨q, hq⟩ := (Spec.map (j.stalkMap y)).surjective p
  change PrimeSpectrum.comap (j.stalkMap y).hom q = p at hq
  have he : q = IsLocalRing.closedPoint (Y.presheaf.stalk y) :=
    Set.mem_singleton_iff.mp (hi (by simpa only [Set.mem_inter_iff, Set.mem_preimage, hq] using hp))
  apply Set.mem_singleton_iff.mpr
  rw [← hq, he]
  apply PrimeSpectrum.ext
  exact IsLocalRing.maximalIdeal_comap (j.stalkMap y).hom

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportEuler
