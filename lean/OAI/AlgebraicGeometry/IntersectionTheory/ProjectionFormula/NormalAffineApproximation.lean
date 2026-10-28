import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrimeLocalization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Approximation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationDivisor

/-! # Normal Affine Approximation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalAffineApproximation

noncomputable section

/-! Arbitrary integer orders can be prescribed at finitely many distinct
codimension-one points of a normal Noetherian affine scheme, in any dimension. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry IsDedekindDomain

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

theorem exists_orders {ι : Type v} [Fintype ι] (x : ι → Spec (.of R))
    (hx : ∀ i, Order.coheight (x i) = 1) (hinj : Function.Injective x) (e : ι → ℤ) :
    ∃ f : (Spec (.of R)).functionField, f ≠ 0 ∧ ∀ i, (Spec (.of R)).ord f (x i) = e i := by
  classical
  by_cases hι : Nonempty ι
  · let := hι
    let P : ι → PrimeSpectrum R := x
    let M := Finite.PrimeLocalization.denominators R P
    let A := Localization M
    have hP (i : ι) : (P i).asIdeal.height = 1 := by
      rw [idealHeight_eq_coheight]
      exact hx i
    let : IsDedekindDomain A := Finite.PrimeLocalization.dedekind R P A hP
    have hp (i : ι) : (Ideal.map (algebraMap R A) (P i).asIdeal).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M A (P i).asIdeal (P i).isPrime
        (Finite.PrimeLocalization.disjoint_denominators R P i)
    let Q : ι → HeightOneSpectrum A := fun i =>
      ⟨Ideal.map (algebraMap R A) (P i).asIdeal, hp i, by
        apply Ideal.ne_bot_of_height_eq_one
        let := hp i
        rw [← IsLocalization.height_under M,
          Finite.PrimeLocalization.under_map R P A, hP]⟩
    let j := Spec.map (CommRingCat.ofHom (algebraMap R A))
    have hQ (i : ι) : j (Affine.Order.branchPoint A (Q i)) = x i := by
      apply PrimeSpectrum.ext
      exact Finite.PrimeLocalization.under_map R P A i
    have hQinj : Function.Injective Q := by
      intro i k hik
      apply hinj
      rw [← hQ i, ← hQ k, hik]
    obtain ⟨g, hg, he⟩ := Affine.Approximation.exists_scheme_orders A Q hQinj e
    let f := (LocalizationDivisor.localizationFieldIso R A M).inv g
    have hfg : LocalizationDivisor.localizationFieldMap R A M f = g :=
      ConcreteCategory.congr_hom (LocalizationDivisor.localizationFieldIso R A M).inv_hom_id g
    refine ⟨f, ?_, fun i => ?_⟩
    · intro hf
      apply hg
      rw [← hfg, hf, map_zero]
    · rw [← hQ i, ← LocalizationDivisor.ord_localization R A M, hfg, he]
  · let : IsEmpty ι := not_nonempty_iff.mp hι
    exact ⟨1, one_ne_zero, fun i => isEmptyElim i⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalAffineApproximation
