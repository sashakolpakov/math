import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalUnitLift
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrimeUnramified
import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift
import OAI.RepresentationTheory.Hecke.RadialDilation.ReindexedPowerBound
import OAI.RepresentationTheory.Hecke.RadialDilation.LocalSwapTopology

/-! # Integral Scalar -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.IntegralScalar.Local

noncomputable section

/-! An actual finite lift supported at q and integral in the fixed
coordinates acts by one nonzero scalar on every full q-unit-ball tensor. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime] {I : Type} [Fintype I] [DecidableEq I]
  {n : ℕ} (e : I ≃ Fin n)

local instance finiteIntegralScalarMeasurableSpace : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance finiteIntegralScalarBorelSpace : BorelSpace ℚ_[q] := ⟨rfl⟩

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem integral_finite_lift_unit_tensors
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n) (hq : 2 < q)
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ_[q]) (m : MpF)
    (hm : D.finite.project m = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q A)
    (hA : ∀ i j, ‖A.val i j‖ ≤ 1) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ h : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := I)),
      D.finite.action m (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeTensor q e (LocalUnitTest.padicUnitTest q n) h) =
        c • RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeTensor q e (LocalUnitTest.padicUnitTest q n) h := by
  obtain ⟨_, _, _, _, hsurj, _⟩ := hLocalWeil ℚ_[q] (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) n hn
    (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter_continuous q D)
    (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter_unitary q D) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter_nontrivial q D)
  obtain ⟨g, hg⟩ := hsurj (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e A))
  have hm' : D.finite.project m = RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e
      (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D) g) := by
    change D.finite.project m = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom
        (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D) g)))
    rw [hg, RepresentationTheory.Hecke.RadialDilation.LocalSwapTopology.Realization.symplecticSwapHom_involutive, RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_symm_apply]
    exact hm
  have hgInt : ∀ i j, ‖(RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D) g).val i j‖ ≤ 1 := by
    intro i j
    rw [hg, RepresentationTheory.Hecke.RadialDilation.ReindexedPowerBound.Realization.symplecticSwapHom_entry]
    exact hA ((e.sumCongr e).symm (Sum.swap i)) ((e.sumCongr e).symm (Sum.swap j))
  obtain ⟨a, ha, hunit⟩ := LocalUnitLift.integral_local_lift_unitTest q n hq
    (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D) (RepresentationTheory.Hecke.RadialDilation.LocalCharacterConductor.Realization.finiteLocalCharacter_eq_one_iff q D) g hgInt
  obtain ⟨ε, hε, hop⟩ := RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.every_indexedPrime_lift_tensor q e D g m hm'
  have hε0 : ε ≠ 0 := by intro h; simp [h] at hε
  refine ⟨ε * a, mul_ne_zero hε0 ha, ?_⟩
  intro h
  have hscale : RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeTensor q e (a • LocalUnitTest.padicUnitTest q n) h =
      a • RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeTensor q e (LocalUnitTest.padicUnitTest q n) h := by
    apply Subtype.ext
    funext x
    rw [RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeTensor_apply]
    change (a * (LocalUnitTest.padicUnitTest q n).val (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeProjection q e x)) * h.val (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x) =
      a * (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeTensor q e (LocalUnitTest.padicUnitTest q n) h).val x
    rw [RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeTensor_apply, mul_assoc]
  rw [hop, hunit, hscale, smul_smul]

include e in
theorem integral_finite_lift_test_scalar
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n) (hq : 2 < q)
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ_[q]) (m : MpF)
    (hm : D.finite.project m = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q A)
    (hA : ∀ i j, ‖A.val i j‖ ≤ 1)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
    (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'),
      ∀ x, φ.val (u + x) = φ.val x) :
    ∃ c : ℂ, c ≠ 0 ∧ D.finite.action m φ = c • φ := by
  obtain ⟨c, hc, hop⟩ := integral_finite_lift_unit_tensors q e hLocalWeil hn hq D A m hm hA
  have ht := PrimeUnramified.Local.finite_test_full_prime_tensor q e φ hsupport N hN hcop hperiod
  exact ⟨c, hc, (congrArg (D.finite.action m) ht).trans
    ((hop (PrimeUnramified.Local.indexedPrimeAwayTest q e φ)).trans (congrArg (fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I => c • f) ht.symm))⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.IntegralScalar.Local
