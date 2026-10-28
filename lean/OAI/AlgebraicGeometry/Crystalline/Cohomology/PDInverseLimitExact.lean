import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimitExact

/-! # PD Inverse Limit Exact -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PDInverseLimitExact.PadicPDInverseLimitExact

noncomputable section

/-!
# Exactness for actual p-power PD quotients

Every transition in the original p-power quotient tower is surjective.
The difference sequence for its explicit PD completion is consequently
short exact, without a Mittag-Leffler hypothesis supplied by the caller.
-/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (E : Type u) [CommRing E] [Algebra (WittVector p k) E]
  (r : E →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) E) =
    (algebraMap k B).comp WittVector.constantCoeff)
  (δ : DividedPowers (RingHom.ker r))
  (hδ : DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) δ
    (algebraMap (WittVector p k) E))

theorem transition_surjective (n m : ℕ) (h : n ≤ m) :
    Function.Surjective (PadicPDP.PadicPDThickening.transition p k B E r hr hbase δ hδ n m h).hom := by
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E m) y, rfl⟩

theorem shortExact :
    (PD.InverseLimitExact.PDInverseLimitExact.sequence p k B
      (PadicPDP.PadicPDThickening.tower p k B E r hr hbase δ hδ)).ShortExact :=
  PD.InverseLimitExact.PDInverseLimitExact.shortExact p k B _
    (fun n => transition_surjective p k B E r hr hbase δ hδ n (n + 1) (Nat.le_succ n))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PDInverseLimitExact.PadicPDInverseLimitExact
