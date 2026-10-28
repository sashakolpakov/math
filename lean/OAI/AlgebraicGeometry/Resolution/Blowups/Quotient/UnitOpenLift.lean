import OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientOpenFrame
import Mathlib.RingTheory.Localization.Ideal

/-! # Unit Open Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.UnitOpenLift.Construction

noncomputable section

/-! Finite units on a closed carrier become units on an actual ambient open through that carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem not_mem_of_surjective_quotient_unit
    {R Q : Type*} [CommRing R] [CommRing Q] (q : R →+* Q)
    (hq : Function.Surjective q) (p : Ideal R) [p.IsPrime]
    (hqp : RingHom.ker q ≤ p) (x : R) (hx : IsUnit (q x)) : x ∉ p := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨r, hr⟩ := hq y
  have hm : x * r - 1 ∈ p := hqp (by
    change q (x * r - 1) = 0
    rw [map_sub, map_mul, hr, hy, map_one, sub_self])
  intro hxp
  exact ‹p.IsPrime›.one_notMem (by
    simpa only [sub_sub_cancel] using p.sub_mem (p.mul_mem_right r hxp) hm)

theorem quotient_unit_pointed_open_lift
    {k R Q : Type u} [CommRing k] [CommRing R] [CommRing Q]
    [Algebra k R] [Algebra k Q] (q : R →ₐ[k] Q) (hq : Function.Surjective q)
    {β : Type v} [Fintype β] (a : β → R) (ha : ∀ j, IsUnit (q (a j)))
    (p : PrimeSpectrum R) (hqp : RingHom.ker q.toRingHom ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (f : R →ₐ[k] S),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (P : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom P = p ∧
      (∀ j, IsUnit (f (a j))) ∧
      ∃ q' : S →ₐ[k] Q, Function.Surjective q' ∧ q'.comp f = q ∧
        RingHom.ker q'.toRingHom = (RingHom.ker q.toRingHom).map f.toRingHom := by
  classical
  let t : R := ∏ j, a j
  have ht : t ∉ p.asIdeal := by
    change t ∈ p.asIdeal.primeCompl
    exact Submonoid.prod_mem _ (fun j _ =>
      not_mem_of_surjective_quotient_unit q.toRingHom hq p.asIdeal hqp (a j) (ha j))
  have hqt : IsUnit (q t) := by
    dsimp only [t]
    rw [map_prod]
    exact IsUnit.prod_univ_iff.mpr ha
  let S := Localization.Away t
  let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  let q' : S →ₐ[k] Q := IsLocalization.Away.liftAlgHom t hqt
  have hq'f (r : R) : q' (f r) = q r := IsLocalization.Away.lift_eq t hqt r
  obtain ⟨P, hP⟩ := Etale.RefinementHelpers.Construction.exists_localization_away_prime t p ht
  refine ⟨.of S, inferInstance, f, IsOpenImmersion.of_isLocalization t, P, hP, ?_,
    q', ?_, ?_, ?_⟩
  · intro j
    exact IsLocalization.Away.isUnit_of_dvd t (Finset.dvd_prod_of_mem a (Finset.mem_univ j))
  · intro y
    obtain ⟨r, hr⟩ := hq y
    exact ⟨f r, (hq'f r).trans hr⟩
  · ext r
    exact hq'f r
  · have he : (RingHom.ker q'.toRingHom).comap f.toRingHom = RingHom.ker q.toRingHom := by
      ext r
      change q' (f r) = 0 ↔ q r = 0
      rw [hq'f]
    have hm := IsLocalization.map_under (Submonoid.powers t) S (RingHom.ker q'.toRingHom)
    change ((RingHom.ker q'.toRingHom).comap f.toRingHom).map f.toRingHom = _ at hm
    rw [he] at hm
    exact hm.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.UnitOpenLift.Construction
