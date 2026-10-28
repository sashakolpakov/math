import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrimeSemilocal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalIdealPrincipal
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Prime Principal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrimePrincipal

noncomputable section

/-! If an ideal is principal at each of finitely many selected primes,
its extension to their common semilocalization is principal. -/

set_option backward.isDefEq.respectTransparency false

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [Nonempty ι] (P : ι → PrimeSpectrum R)

theorem principal (I : Ideal R)
    (h : ∀ i, (I.map (algebraMap R (Localization.AtPrime (P i).asIdeal))).IsPrincipal) :
    (I.map (algebraMap R (Localization (PrimeLocalization.denominators R P)))).IsPrincipal := by
  let M := PrimeLocalization.denominators R P
  let A := Localization M
  let : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A
    (PrimeLocalization.denominators_le R P)
  let : Finite (MaximalSpectrum A) := PrimeSemilocal.finite_maximals R P A
  apply SemilocalIdealPrincipal.of_local_principal A
  intro q hq
  let B := Localization.AtPrime q
  obtain ⟨i, hi⟩ := PrimeSemilocal.maximal_contraction R P A q
  let : IsLocalization.AtPrime B (P i).asIdeal := by
    change IsLocalization (P i).asIdeal.primeCompl B
    have hc : (q.under R).primeCompl = (P i).asIdeal.primeCompl := by
      ext x
      change (x ∉ q.under R) ↔ (x ∉ (P i).asIdeal)
      rw [hi]
    exact hc ▸ IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M B q
  let e : Localization.AtPrime (P i).asIdeal ≃ₐ[R] B :=
    IsLocalization.algEquiv (P i).asIdeal.primeCompl _ _
  obtain ⟨r, hr⟩ := (h i).principal
  have hmap : (I.map (algebraMap R (Localization.AtPrime (P i).asIdeal))).map e.toRingHom =
      I.map (algebraMap R B) := by
    rw [Ideal.map_map]
    congr 1
    exact e.toAlgHom.comp_algebraMap
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R A B]
  refine ⟨e r, ?_⟩
  rw [← hmap, hr, Ideal.map_span, Set.image_singleton]
  rfl

theorem exists_generator (I : Ideal R) (hI : I ≠ ⊥)
    (h : ∀ i, (I.map (algebraMap R (Localization.AtPrime (P i).asIdeal))).IsPrincipal) :
    ∃ r : R, r ∈ I ∧ r ≠ 0 ∧ ∀ i,
      I.map (algebraMap R (Localization.AtPrime (P i).asIdeal)) =
        Ideal.span {algebraMap R (Localization.AtPrime (P i).asIdeal) r} := by
  let M := PrimeLocalization.denominators R P
  let A := Localization M
  have hinj : Function.Injective (algebraMap R A) := IsLocalization.injective A
    (PrimeLocalization.denominators_le R P)
  obtain ⟨g, hg⟩ := (PrimePrincipal.principal R P I h).principal
  have hg0 : g ≠ 0 := by
    intro hg0
    apply hI
    apply (Ideal.map_eq_bot_iff_of_injective hinj).mp
    rw [hg, hg0, Submodule.span_zero_singleton]
  have hgmem : g ∈ I.map (algebraMap R A) := hg ▸ Submodule.mem_span_singleton_self g
  obtain ⟨⟨⟨r, hr⟩, s⟩, hgs⟩ := (IsLocalization.mem_map_algebraMap_iff M A).mp hgmem
  change g * algebraMap R A s = algebraMap R A r at hgs
  have hs : IsUnit (algebraMap R A s) := IsLocalization.map_units A s
  have he : I.map (algebraMap R A) = Ideal.span {algebraMap R A r} := by
    rw [← hgs, Ideal.span_singleton_mul_right_unit hs]
    exact hg
  refine ⟨r, hr, ?_, fun i => ?_⟩
  · intro hr0
    apply hg0
    apply hs.mul_left_eq_zero.mp
    rw [hgs, hr0, map_zero]
  · let T := Localization.AtPrime (P i).asIdeal
    have hle : M ≤ (P i).asIdeal.primeCompl := iInf_le _ i
    let : Algebra A T := IsLocalization.localizationAlgebraOfSubmonoidLe
      A T M (P i).asIdeal.primeCompl hle
    let : IsScalarTower R A T := IsLocalization.localization_isScalarTower_of_submonoid_le
      A T M (P i).asIdeal.primeCompl hle
    have hmap := congrArg (Ideal.map (algebraMap A T)) he
    simpa only [Ideal.map_map, ← IsScalarTower.algebraMap_eq R A T, Ideal.map_span,
      Set.image_singleton, ← IsScalarTower.algebraMap_apply R A T] using hmap

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrimePrincipal
