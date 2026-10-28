import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AdicIdealContainment

/-! # Formal Coefficient Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FormalCoefficientIdeal

noncomputable section

/-! Compatible coefficient ideals on the finite thickenings of a complete
Noetherian base determine a coefficient ideal for a proper source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (R : CommRingCat.{u}) [IsNoetherianRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec R) [IsProper f]

theorem proper_formal_coefficient_ideal (I : Ideal R) [IsAdicComplete I R]
    (K : X.IdealSheafData)
    (h : ∀ n : ℕ, ∃ J : Ideal R, I ^ n ≤ J ∧
      ∀ L : Ideal R, I ^ n ≤ L →
        (K ≤ ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm L).comap f ↔ J ≤ L)) :
    ∃ J : Ideal R, ∀ L : Ideal R,
      K ≤ ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm L).comap f ↔ J ≤ L := by
  classical
  choose J hpow htest using h
  have hself (n : ℕ) : K ≤ ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm (J n)).comap f :=
    (htest n (J n) (hpow n)).mpr le_rfl
  have hmono {L M : Ideal R} (hLM : L ≤ M) :
      ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm L).comap f ≤
        ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm M).comap f :=
    Scheme.IdealSheafData.comap_mono f ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm.monotone hLM)
  have hstep (n : ℕ) : J (n + 1) ⊔ I ^ n = J n := by
    apply le_antisymm
    · apply sup_le _ (hpow n)
      exact (htest (n + 1) (J n)
        ((Ideal.pow_le_pow_right n.le_succ).trans (hpow n))).mp (hself n)
    · apply (htest n _ le_sup_right).mp
      exact (hself (n + 1)).trans (hmono le_sup_left)
  have hzero : K ≤ ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm (⨅ n, J n)).comap f := by
    apply AdicIdealContainment.proper_adic_ideal_containment R f I (IsAdicComplete.le_jacobson_bot I)
    intro n
    rw [CompatibleAdicIdeals.compatibleAdicIdeals_intersection I J hpow hstep]
    exact hself n
  refine ⟨⨅ n, J n, fun L => ⟨?_, fun hL => hzero.trans (hmono hL)⟩⟩
  intro hL
  apply (AdicIdealSeparation.compatibleAdicIdeals_le_iff I J hpow hstep L).mpr
  intro n
  exact (htest n _ le_sup_right).mp (hL.trans (hmono le_sup_left))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FormalCoefficientIdeal
