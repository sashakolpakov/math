import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MinimalPrimeFiltration
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Tor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BaseChangeSupport

/-! # Point Support Localization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointSupportLocalization

noncomputable section

/-! Localizing a finite module supported at one maximal point preserves
its native length. The proof uses the same prime filtration before and
after localization, whose factors are all that point's residue field. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  (p : PrimeSpectrum R) [p.asIdeal.IsMaximal]

theorem length (M : ModuleCat.{u} R) [Module.Finite R M]
    (hp : Module.support R M ⊆ {p}) :
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M) =
      Module.length R M := by
  classical
  obtain ⟨s, h₀, ht⟩ := IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime R M
  choose q e using fun i => (s.step i).2
  have hq (i : Fin s.length) : q i = p := by
    have hsup : Module.support R (R ⧸ (q i).asIdeal) ⊆ Module.support R M := by
      rw [← (e i).some.support_eq]
      exact (Module.support_subset_of_surjective ((s i.castSucc).submoduleOf (s i.succ)).mkQ
        (Submodule.mkQ_surjective _)).trans
        (Module.support_subset_of_injective (s i.succ).subtype (Submodule.subtype_injective _))
    exact Set.mem_singleton_iff.mp (hp (hsup (MinimalPrimeFiltration.prime_mem_support R (q i))))
  change FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) M = _
  rw [FiltrationBaseLength.filtration_sum R (Localization.AtPrime p.asIdeal) M s h₀ ht]
  have hself := FiltrationBaseLength.filtration_sum R R M s h₀ ht
  have hid : FiltrationBaseLength.length R R M = Module.length R M := (TensorProduct.lid R M).length_eq
  rw [← hid, hself]
  apply Finset.sum_congr rfl
  intro i _
  rw [FiltrationBaseLength.length_iso R (Localization.AtPrime p.asIdeal) (e i).some.toModuleIso,
    FiltrationBaseLength.length_iso R R (e i).some.toModuleIso, hq i]
  rw [MinimalPrimeFiltration.localized_prime_length R p p (fun _ => rfl), ite_eq_left rfl]
  change 1 = Module.length R (R ⊗[R] (R ⧸ p.asIdeal))
  rw [(TensorProduct.lid R (R ⧸ p.asIdeal)).length_eq]
  rw [Module.length_eq_of_surjective (R := R ⧸ p.asIdeal) (S := R) (M := R ⧸ p.asIdeal)
    (show Function.Surjective (algebraMap R (R ⧸ p.asIdeal)) from Ideal.Quotient.mk_surjective)]
  let : Field (R ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  exact (Module.length_eq_one (R ⧸ p.asIdeal) (R ⧸ p.asIdeal)).symm

theorem tor_length (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (hp : Module.support R M ∩ Module.support R N ⊆ {p}) (n : ℕ) :
    Module.length (Localization.AtPrime p.asIdeal)
      (((Tor (ModuleCat (Localization.AtPrime p.asIdeal)) n).obj
        ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj M)).obj
        ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj N)) =
      Module.length R (((Tor (ModuleCat R) n).obj M).obj N) := by
  let := ProjectionFormula.Finite.Tor.finite R M N n
  exact (Flat.Extension.torBaseChangeIso R (Localization.AtPrime p.asIdeal) M N n).toLinearEquiv.length_eq.trans
    (PointSupportLocalization.length R p (((Tor (ModuleCat R) n).obj M).obj N) ((ProjectionFormula.Tor.Support.support_subset R M N n).trans hp))

theorem euler (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (hp : Module.support R M ∩ Module.support R N ⊆ {p}) (d : ℕ) :
    ProjectionFormula.Tor.Euler.euler (Localization.AtPrime p.asIdeal)
      ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj M)
      ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj N) d =
      ProjectionFormula.Tor.Euler.euler R M N d := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ i * (l.toNat : ℚ)) (tor_length R p M N hp i)

omit [p.asIdeal.IsMaximal] [IsNoetherianRing R] in
theorem isolated (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (hp : Module.support R M ∩ Module.support R N ⊆ {p}) :
    Module.support (Localization.AtPrime p.asIdeal)
        ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj M) ∩
      Module.support (Localization.AtPrime p.asIdeal)
        ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj N) ⊆
      {IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)} := by
  intro q hq
  have he : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q = p :=
    Set.mem_singleton_iff.mp (hp ⟨BaseChangeSupport.mem_image R (Localization.AtPrime p.asIdeal) M q hq.1,
      BaseChangeSupport.mem_image R (Localization.AtPrime p.asIdeal) N q hq.2⟩)
  apply Set.mem_singleton_iff.mpr
  apply PrimeSpectrum.ext
  exact Localization.AtPrime.eq_maximalIdeal_iff_under_eq.mp (congrArg PrimeSpectrum.asIdeal he)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointSupportLocalization
