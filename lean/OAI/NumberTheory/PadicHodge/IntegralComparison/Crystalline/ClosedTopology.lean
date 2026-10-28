import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization

/-! # Closed Topology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ClosedTopology

noncomputable section

/-!
# IntegralComparison: topology of nilpotent closed crystalline subschemes

Every ambient point lies on the closed subscheme. A principal crystalline
localization maps its closed points into the corresponding principal open
of the original closed subscheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable (T : BigCrystallineSite.Object p B J δ f)

lemma quotientSpec_surjective : Function.Surjective
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk T.ideal))) := by
  intro x
  change x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk T.ideal))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
  change RingHom.ker (Ideal.Quotient.mk T.ideal) ≤ x.asIdeal
  rw [Ideal.mk_ker]
  intro a ha
  exact (nilpotent_iff_mem_prime.mp (T.nilIdeal a ha)) x.asIdeal x.isPrime

lemma closedMap_mem_basicOpen (r : T.ring)
    (z : Spec (CommRingCat.of (Localization.Ring T r ⧸ Localization.ideal T r))) :
    Localization.closedMap T r z ∈ PrimeSpectrum.basicOpen (Ideal.Quotient.mk T.ideal r) := by
  let : z.asIdeal.IsPrime := z.isPrime
  change Ideal.Quotient.mk (Localization.ideal T r) (algebraMap T.ring (Localization.Ring T r) r) ∉ z.asIdeal
  exact Ideal.notMem_of_isUnit _ ((IsLocalization.Away.algebraMap_isUnit r).map
    (Ideal.Quotient.mk (Localization.ideal T r)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ClosedTopology
