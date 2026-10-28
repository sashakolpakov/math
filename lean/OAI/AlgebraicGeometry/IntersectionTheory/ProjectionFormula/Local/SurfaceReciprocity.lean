import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalSurfaceOrderSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.EulerTransport

/-! # Surface Reciprocity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SurfaceReciprocity

noncomputable section

/-! Local reciprocity on any Noetherian local surface domain, including
nonnormal surfaces. Native Tor symmetry retains the embedded-point
correction terms and removes any regularity assumption on the pair. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

theorem exists_euler_sum (hdim : (maximalIdeal R).height = 2)
    (f g : R) (hf : f ≠ 0) (hg : g ≠ 0)
    (havoid : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → f ∈ p → g ∉ p) :
    ∃ S : Finset (PrimeSpectrum R),
      (∀ p ∈ S, p.asIdeal.height = 1 ∧ f ∈ p.asIdeal) ∧
      (∀ p : PrimeSpectrum R, p.asIdeal.height = 1 → p ∉ S →
        Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) f) = 0) ∧
      Tor.Euler.euler R (.of R (QuotSMulTop f R)) (.of R (QuotSMulTop g R)) 1 =
        ∑ p ∈ S, ((Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) f)).toNat : ℚ) *
          ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal g)).toNat : ℚ) := by
  let N := ModuleCat.of R (QuotSMulTop g R)
  let : HasProjectiveDimensionLE N 1 :=
    Regular.LocalTwoBound.quotient_bound R (.of R R) g (IsSMulRegular.of_ne_zero hg) 0
  have hisolated : Module.support R (QuotSMulTop f R) ∩ Module.support R N ⊆ {closedPoint R} := by
    intro p hp
    have hfp : f ∈ p.asIdeal := by
      have h := hp.1
      rw [Module.support_quotSMulTop] at h
      exact h.2 (Set.mem_singleton f)
    have hgp : g ∈ p.asIdeal := by
      have h := hp.2
      change p ∈ Module.support R (QuotSMulTop g R) at h
      rw [Module.support_quotSMulTop] at h
      exact h.2 (Set.mem_singleton g)
    have hp₀ : p.asIdeal ≠ ⊥ := by
      intro hz
      exact hf (by simpa only [hz, Submodule.mem_bot] using hfp)
    rcases SurfacePrimeEuler.prime_height_one_or_maximal R hdim p hp₀ with hh | hh
    · exact (havoid p.asIdeal hh hfp hgp).elim
    · exact Set.mem_singleton_iff.mpr (PrimeSpectrum.ext hh)
  have hN : ∀ x : N, ∃ a : R, a ≠ 0 ∧ a • x = 0 := by
    intro x
    refine ⟨g, hg, ?_⟩
    let e := NormalSurfaceOrderSum.principalQuotientEquiv R g
    apply e.injective
    rw [map_smul, map_zero]
    exact PrimeQuotientLocalization.annihilated R (Ideal.span {g}) g
      (Ideal.subset_span (Set.mem_singleton g)) (e x)
  obtain ⟨S, hS, hout, he⟩ :=
    WeightedDivisorEuler.exists_order_sum R hdim f hf N 1 hN hisolated
  refine ⟨S, hS, hout, he.trans ?_⟩
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  exact Principal.Order.euler_eq_order R (R ⧸ p.asIdeal)
    Ideal.Quotient.mk_surjective g (IsSMulRegular.of_ne_zero hg)
    (Ideal.Quotient.eq_zero_iff_mem.not.mpr (havoid p.asIdeal (hS p hp).1 (hS p hp).2)) 1

theorem order_sums_eq (hdim : (maximalIdeal R).height = 2)
    (f g : R) (hf : f ≠ 0) (hg : g ≠ 0)
    (havoid : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → f ∈ p → g ∉ p) :
    ∃ S T : Finset (PrimeSpectrum R),
      (∀ p ∈ S, p.asIdeal.height = 1 ∧ f ∈ p.asIdeal) ∧
      (∀ p ∈ T, p.asIdeal.height = 1 ∧ g ∈ p.asIdeal) ∧
      (∀ p : PrimeSpectrum R, p.asIdeal.height = 1 → p ∉ S →
        Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) f) = 0) ∧
      (∀ p : PrimeSpectrum R, p.asIdeal.height = 1 → p ∉ T →
        Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) g) = 0) ∧
      (∑ p ∈ S, ((Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) f)).toNat : ℚ) *
          ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal g)).toNat : ℚ)) =
        ∑ p ∈ T, ((Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) g)).toNat : ℚ) *
          ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal f)).toNat : ℚ) := by
  obtain ⟨S, hS, houtS, heS⟩ := exists_euler_sum R hdim f g hf hg havoid
  obtain ⟨T, hT, houtT, heT⟩ := exists_euler_sum R hdim g f hg hf
    (fun p _ hp hgp hfp => havoid p hp hfp hgp)
  refine ⟨S, T, hS, hT, houtS, houtT, heS.symm.trans ?_⟩
  rw [Tor.EulerTransport.comm R (.of R (QuotSMulTop f R)) (.of R (QuotSMulTop g R)) 1]
  exact heT

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SurfaceReciprocity
