import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality
import OAI.Analysis.DifferentialForms.Manifold.PurePullback

/-! # Cycle Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleForms.CM.Abelian

noncomputable section

/-! Vanishing of the off-diagonal top-degree classes used to test geometric cycles. -/

open _root_.CategoryTheory

theorem pureBettiClass_eq_zero_of_offDiagonal_top
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (hdim : p + q = 2 * V.complexDimension) (hpq : p ≠ q)
    (a : V.complexCohomology (p + q))
    (ha : a ∈ V.pureBettiSubspace p q) : a = 0 := by
  obtain ⟨ω, hω, rfl⟩ := (V.mem_pureBettiSubspace_iff p q a).mp ha
  have htype : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace p q ω.val :=
    (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mpr hω
  have hz : (ω.val : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace (p + q)) = 0 :=
    Analysis.DifferentialForms.Manifold.PurePullback.pureManifoldForm_eq_zero_of_offDiagonal_top htype
      (by simpa only [V.analyticModel_complex_finrank] using hdim) hpq
  have hω0 : ω = 0 := Subtype.ext (Subtype.ext hz)
  rw [hω0]
  simp [Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamClass]

theorem algebraicPullback_eq_zero_of_offDiagonal_top
    {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : R.toOver ⟶ X.toOver)
    (p q : ℕ) (hdim : p + q = 2 * R.complexDimension) (hpq : p ≠ q)
    (a : X.complexCohomology (p + q))
    (ha : a ∈ X.pureBettiSubspace p q) :
    R.complexBettiPullback f (p + q) a = 0 :=
  pureBettiClass_eq_zero_of_offDiagonal_top R p q hdim hpq _
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace f p q ha)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleForms.CM.Abelian
