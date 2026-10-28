import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.RegularLocal
import Mathlib.RingTheory.Flat.Localization

/-! # Regular Ring -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.RegularRing

noncomputable section

/-! Regularity passes through the actual flat unramified chart algebras
and through arbitrary local localizations of these algebras. -/

set_option backward.isDefEq.respectTransparency false

universe u v w

theorem regular (R : Type u) (S : Type v) [CommRing R] [IsRegularRing R]
    [CommRing S] [IsNoetherianRing S] [Algebra R S] [Module.Flat R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] : IsRegularRing S := by
  apply isRegularRing_iff.mpr
  intro p hp
  let q := p.under R
  let T := Localization.AtPrime q
  let A := Localization.AtPrime p
  let : Algebra T A := Localization.AtPrime.algebraOfLiesOver q p
  let : IsLocalHom (algebraMap T A) := by
    change IsLocalHom (Localization.localRingHom q p (algebraMap R S) Ideal.LiesOver.over)
    exact Localization.isLocalHom_localRingHom q p (algebraMap R S) Ideal.LiesOver.over
  let : Algebra.FormallyUnramified T A := Algebra.FormallyUnramified.of_restrictScalars R T A
  let : Algebra.EssFiniteType T A := Algebra.EssFiniteType.of_comp R T A
  exact RegularLocal.regular T A

theorem local_localization (S : Type u) [CommRing S] [IsRegularRing S]
    (A : Type v) [CommRing A] [IsLocalRing A] [Algebra S A]
    (M : Submonoid S) [IsLocalization M A] : IsRegularLocalRing A := by
  let p := (IsLocalRing.maximalIdeal A).comap (algebraMap S A)
  let : p.IsPrime := Ideal.IsPrime.comap _
  have hm : M ≤ p.primeCompl := by
    intro a ha
    exact IsLocalRing.notMem_maximalIdeal.mpr (IsLocalization.map_units A (⟨a, ha⟩ : M))
  let : IsLocalization.AtPrime A p := IsLocalization.of_le M p.primeCompl hm
    (fun a ha => IsLocalRing.notMem_maximalIdeal.mp ha)
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A).toRingEquiv

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.RegularRing
