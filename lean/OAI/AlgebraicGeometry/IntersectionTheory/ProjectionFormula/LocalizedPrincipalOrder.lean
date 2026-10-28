import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrimePrincipal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfacePrimeEuler

/-! # Localized Principal Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedPrincipalOrder

noncomputable section

/-! A simultaneous local equation has coefficient one at its own prime
divisor and zero at every other prime divisor through the selected points. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

omit [IsDomain R] [IsNoetherianRing R] in
theorem equation_of_le (I : Ideal R) (p q : PrimeSpectrum R) (hqp : q ≤ p)
    (r : R)
    (h : I.map (algebraMap R (Localization.AtPrime p.asIdeal)) =
      Ideal.span {algebraMap R (Localization.AtPrime p.asIdeal) r}) :
    I.map (algebraMap R (Localization.AtPrime q.asIdeal)) =
      Ideal.span {algebraMap R (Localization.AtPrime q.asIdeal) r} := by
  let A := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime q.asIdeal
  have hle : p.asIdeal.primeCompl ≤ q.asIdeal.primeCompl := fun _ hx hq => hx (hqp hq)
  let : Algebra A B := IsLocalization.localizationAlgebraOfSubmonoidLe
    A B p.asIdeal.primeCompl q.asIdeal.primeCompl hle
  let : IsScalarTower R A B := IsLocalization.localization_isScalarTower_of_submonoid_le
    A B p.asIdeal.primeCompl q.asIdeal.primeCompl hle
  change I.map (algebraMap R A) = Ideal.span {algebraMap R A r} at h
  have he := congrArg (Ideal.map (algebraMap A B)) h
  simpa only [Ideal.map_map, ← IsScalarTower.algebraMap_eq R A B, Ideal.map_span,
    Set.image_singleton, ← IsScalarTower.algebraMap_apply R A B] using he

omit [IsDomain R] in
theorem order (p q : PrimeSpectrum R) (hp : p.asIdeal.height = 1)
    (hq : q.asIdeal.height = 1) (r : R)
    (h : p.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)) =
      Ideal.span {algebraMap R (Localization.AtPrime q.asIdeal) r}) :
    Ring.ord (Localization.AtPrime q.asIdeal)
      (algebraMap R (Localization.AtPrime q.asIdeal) r) = if q = p then 1 else 0 := by
  classical
  by_cases he : q = p
  · subst q
    rw [ite_eq_left rfl, Ring.ord, ← h, Localization.AtPrime.map_eq_maximalIdeal]
    exact SurfacePrimeEuler.residue_quotient_length _
  · rw [ite_eq_right he]
    have hn : ¬p.asIdeal ≤ q.asIdeal := by
      intro hle
      exact he (PrimeSpectrum.ext (p.asIdeal.eq_of_le_of_height_le hle (by rw [hp, hq])).symm)
    obtain ⟨a, ha, haq⟩ := SetLike.not_le_iff_exists.mp hn
    have ht : p.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha)
        (IsLocalization.map_units _ (⟨a, haq⟩ : q.asIdeal.primeCompl))
    exact Ring.ord_of_isUnit (Ideal.span_singleton_eq_top.mp (h.symm.trans ht))

theorem exists_orders {ι : Type v} [Fintype ι] [Nonempty ι]
    (P : ι → PrimeSpectrum R) (p : PrimeSpectrum R) (hp : p.asIdeal.height = 1)
    (h : ∀ i, (p.asIdeal.map (algebraMap R (Localization.AtPrime (P i).asIdeal))).IsPrincipal) :
    ∃ r : R, r ≠ 0 ∧ ∀ i (q : PrimeSpectrum R), q.asIdeal.height = 1 → q ≤ P i →
      (Spec (.of R)).ord (StructureSheaf.toStalk R (genericPoint (Spec (.of R))) r) q =
        if q = p then 1 else 0 := by
  classical
  obtain ⟨r, _, hr, he⟩ := Finite.PrimePrincipal.exists_generator R P p.asIdeal
    (Ideal.ne_bot_of_height_eq_one hp) h
  refine ⟨r, hr, fun i q hq hqp => ?_⟩
  rw [Affine.PrincipalOrder.affine_order R q hq r hr,
    order R p q hp hq r (equation_of_le R p.asIdeal (P i) q hqp r (he i))]
  split_ifs <;> norm_num

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedPrincipalOrder
