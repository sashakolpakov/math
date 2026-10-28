import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiltrationBaseLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfacePrimeEuler
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Prime Filtration Multiplicity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationMultiplicity

noncomputable section

/-! The number of occurrences of a height-one prime in a torsion prime
filtration is its actual localized module length. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped TensorProduct Classical

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem localized_prime_length (p q : PrimeSpectrum R) (hp : p.asIdeal.height = 1)
    (hq : q.asIdeal ≠ ⊥) :
    FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) (.of R (R ⧸ q.asIdeal)) =
      if q = p then 1 else 0 := by
  let A := Localization.AtPrime p.asIdeal
  change Module.length A (A ⊗[R] (R ⧸ q.asIdeal)) = _
  rw [← (Ideal.qoutMapEquivTensorQout (R := R) (I := q.asIdeal) A).length_eq]
  by_cases he : q = p
  · subst q
    rw [ite_eq_left rfl, Localization.AtPrime.map_eq_maximalIdeal,
      SurfacePrimeEuler.residue_quotient_length]
  · rw [ite_eq_right he]
    have hnot : ¬ q.asIdeal ≤ p.asIdeal := by
      intro h
      apply he
      apply PrimeSpectrum.ext
      apply q.asIdeal.eq_of_le_of_height_le h
      rw [hp]
      exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hq)
    have htop : q.asIdeal.map (algebraMap R A) = ⊤ := by
      apply IsLocalization.map_eq_top_of_not_subset p.asIdeal.primeCompl A
      intro h
      apply hnot
      intro a ha
      exact not_not.mp (h ha)
    rw [htop]
    exact Module.length_eq_zero

theorem filtration_count (M : ModuleCat.{u} R)
    (s : RelSeries {(L, K) | Submodule.IsQuotientEquivQuotientPrime (A := R) (M := M) L K})
    (h₀ : s.head = ⊥) (ht : s.last = ⊤)
    (q : Fin s.length → PrimeSpectrum R)
    (e : ∀ i : Fin s.length,
      (s i.succ ⧸ (s i.castSucc).submoduleOf (s i.succ)) ≃ₗ[R] R ⧸ (q i).asIdeal)
    (hq : ∀ i, (q i).asIdeal ≠ ⊥) (p : PrimeSpectrum R) (hp : p.asIdeal.height = 1) :
    FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) M =
      (Finset.univ.filter (fun i => q i = p)).card := by
  let A := Localization.AtPrime p.asIdeal
  let : Module.Flat R A := IsLocalization.flat A p.asIdeal.primeCompl
  rw [FiltrationBaseLength.filtration_sum R A M s h₀ ht]
  have h (i : Fin s.length) :
      FiltrationBaseLength.length R A (.of R (s i.succ ⧸ (s i.castSucc).submoduleOf (s i.succ))) =
        if q i = p then 1 else 0 :=
    (FiltrationBaseLength.length_iso R A (e i).toModuleIso).trans
      (localized_prime_length R p (q i) hp (hq i))
  simp_rw [h]
  simp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationMultiplicity
