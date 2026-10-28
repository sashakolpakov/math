import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalOrder
import Mathlib.RingTheory.Nullstellensatz

/-! # Closed Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedOrder.Construction

noncomputable section

/-! Local order at every closed point of an étale polynomial algebra over an algebraically closed field. -/

open _root_.MvPolynomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsJacobsonRing A] [Algebra.FiniteType A B]

/-- Maximal ideals contract to maximal ideals under finite type maps from
a Jacobson ring. We apply Zariski's lemma to the residue field. -/
theorem finiteType_maximalIdeal_under (q : Ideal B) [q.IsMaximal] :
    (q.under A).IsMaximal := by
  let : Field (B ⧸ q) := Ideal.Quotient.field q
  let : Module.Finite A (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing A (B ⧸ q)
  have h : ((⊥ : Ideal (B ⧸ q)).under A).IsMaximal := inferInstance
  have he : (⊥ : Ideal (B ⧸ q)).under A = q.under A := by
    ext a
    simp only [Ideal.under_def, Ideal.mem_comap, Submodule.mem_bot,
      IsScalarTower.algebraMap_apply A B (B ⧸ q), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
  rwa [he] at h

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.FiniteType (MvPolynomial σ K) S]

/-- Every closed point of a finite type polynomial algebra lies over a
rational point of affine space when the coefficient field is algebraically closed. -/
theorem finiteType_maximalIdeal_liesOver_polynomialPoint (q : Ideal S) [q.IsMaximal] :
    ∃ x : σ → K, q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x) := by
  have hq := finiteType_maximalIdeal_under (A := MvPolynomial σ K) q
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hq
  refine ⟨x, ⟨?_⟩⟩
  rw [hx]
  ext p
  simp [PolynomialTranslation.Construction.polynomialPointIdeal]

variable [CharZero K] [Fintype σ] [DecidableEq σ]
  [Algebra.Etale (MvPolynomial σ K) S]

include σ K in
/-- Differential equations on the affine ring detect order at every
closed point, without choosing a polynomial point in the statement. -/
theorem etale_closedPoint_order_iff_differentialIdeal (J : Ideal S)
    (q : Ideal S) [q.IsMaximal] (b : ℕ) :
    J.map (algebraMap S (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (b + 1) ↔
      DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J b ≤ q := by
  obtain ⟨x, hx⟩ := finiteType_maximalIdeal_liesOver_polynomialPoint (K := K) (σ := σ) q
  let : q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x) := hx
  exact LocalOrder.Construction.etale_local_order_iff_differentialIdeal J x q b

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedOrder.Construction
