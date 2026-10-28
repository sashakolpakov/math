import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

/-! # Affine Chart Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineChartDimension

noncomputable section

/-! The free coordinates in a genuine principal standard-smooth
neighborhood have the native affine manifold's generic dimension. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

theorem principalSmooth_free_dimension {S : Type*} [CommRing S] [Algebra ℂ S] [IsDomain S]
    [Algebra.Smooth ℂ S]
    (g : S) (hg : g ≠ 0) {n m : ℕ}
    (P : Algebra.SubmersivePresentation ℂ (Localization.Away g) (Fin n) (Fin m)) :
    Fintype.card (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map) = Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S := by
  let : IsDomain (Localization.Away g) := Localization.Away.isDomain hg
  have hcount := Nat.card_congr (ComplexPoints.Analytic.JacobianRegularity.selectedIndexEquiv P.map P.map_inj)
  have hsum : Nat.card (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map) + m = n := by
    simpa only [Nat.card_sum, Nat.card_fin] using hcount
  have hfree : Fintype.card (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map) = n - m :=
    Fintype.card_eq_nat_card.trans (by omega)
  have hdim : P.dimension = Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S :=
    Foundations.Scheme.SmoothDomainDimension.Algebraic.localized_submersive_dimension (R := ℂ) (S := S) (T := Localization.Away g)
      (ι := Fin n) (σ := Fin m) (Submonoid.powers g) P
  have hpn : P.dimension = n - m := by
    simp only [Algebra.Presentation.dimension, Nat.card_fin]
  exact hfree.trans (hpn.symm.trans hdim)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineChartDimension
