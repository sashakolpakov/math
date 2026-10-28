import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalPrincipalRegular
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.WeightedDivisorEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.LocalTwoBound
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrincipalLeft

/-! # Normal Surface Order Sum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalSurfaceOrderSum

noncomputable section

/-! On a possibly singular normal local surface, the colength of two
functions with no common divisor is the sum of the actual orders of the
second function along the height-one components of the first. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory IsLocalRing
open scoped Pointwise

universe u

variable (R : Type u) [CommRing R]

def principalQuotientEquiv (g : R) : QuotSMulTop g R ≃ₗ[R] R ⧸ Ideal.span {g} :=
  Submodule.quotEquivOfEq _ _ (by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])

variable [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]

theorem exists_order_sum (hdim : (maximalIdeal R).height = 2)
    (f g : R) (hf : f ≠ 0) (hg : g ≠ 0)
    (havoid : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → f ∈ p → g ∉ p) :
    ∃ S : Finset (PrimeSpectrum R),
      (∀ p ∈ S, p.asIdeal.height = 1 ∧ f ∈ p.asIdeal) ∧
      (∀ p : PrimeSpectrum R, p.asIdeal.height = 1 → p ∉ S →
        Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) f) = 0) ∧
      ((Module.length R (R ⧸ Ideal.span {g, f})).toNat : ℚ) =
        ∑ p ∈ S, ((Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) f)).toNat : ℚ) *
          ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal g)).toNat : ℚ) := by
  let N := ModuleCat.of R (R ⧸ Ideal.span {g})
  let e := principalQuotientEquiv R g
  let : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop g R)) 1 :=
    Regular.LocalTwoBound.quotient_bound R (.of R R) g (IsSMulRegular.of_ne_zero hg) 0
  let : HasProjectiveDimensionLE N 1 := hasProjectiveDimensionLT_of_iso e.toModuleIso 2
  have hisolated : Module.support R (QuotSMulTop f R) ∩ Module.support R N ⊆ {closedPoint R} := by
    intro p hp
    have hfp : f ∈ p.asIdeal := by
      have h := hp.1
      rw [Module.support_quotSMulTop] at h
      exact h.2 (Set.mem_singleton f)
    have hgp : g ∈ p.asIdeal := by
      have h := hp.2
      change p ∈ Module.support R (R ⧸ Ideal.span {g}) at h
      simp only [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker,
        PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at h
      exact h (Ideal.subset_span (Set.mem_singleton g))
    have hp₀ : p.asIdeal ≠ ⊥ := by
      intro hz
      exact hf (by simpa only [hz, Submodule.mem_bot] using hfp)
    rcases SurfacePrimeEuler.prime_height_one_or_maximal R hdim p hp₀ with hh | hh
    · exact (havoid p.asIdeal hh hfp hgp).elim
    · exact Set.mem_singleton_iff.mpr (PrimeSpectrum.ext hh)
  have hN : ∀ x : N, ∃ a : R, a ≠ 0 ∧ a • x = 0 := fun x =>
    ⟨g, hg, PrimeQuotientLocalization.annihilated R (Ideal.span {g}) g
      (Ideal.subset_span (Set.mem_singleton g)) x⟩
  obtain ⟨S, hS, hout, he⟩ :=
    WeightedDivisorEuler.exists_order_sum R hdim f hf N 1 hN hisolated
  have hreg : IsSMulRegular N f := NormalPrincipalRegular.regular R g f hg
    (fun p _ hp hgp hfp => havoid p hp hfp hgp)
  have heuler : Tor.Euler.euler R (.of R (QuotSMulTop f R)) N 1 =
      ((Module.length R (QuotSMulTop f N)).toNat : ℚ) :=
    Principal.TorLeft.euler_length R f (IsSMulRegular.of_ne_zero hf) N hreg 1
  have hlength : Module.length R (QuotSMulTop f N) = Module.length R (R ⧸ Ideal.span {g, f}) :=
    (Regular.LocalTwoBound.quotientPairEquiv R g f).length_eq
  refine ⟨S, hS, hout, ?_⟩
  rw [← hlength, ← heuler, he]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  exact Principal.Order.euler_eq_order_of_equiv R (R ⧸ p.asIdeal)
    Ideal.Quotient.mk_surjective g (IsSMulRegular.of_ne_zero hg)
    (Ideal.Quotient.eq_zero_iff_mem.not.mpr (havoid p.asIdeal (hS p hp).1 (hS p hp).2))
    N e.symm 1

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalSurfaceOrderSum
