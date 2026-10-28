import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUltra
import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierCovariance

/-! # Fourier Involution -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.FourierInvolution.Construction

noncomputable section

/-! Fourier inversion up to a nonzero scalar from the proved algebraic
commutant theorem and Fourier injectivity. -/

open _root_.MeasureTheory
open scoped BigOperators

def positionNegation {F : Type} [NormedField F] (d : ℕ) :
    Weil.Local.FunctionsMetaplectic.Construction.Position F d ≃ₜ+ Weil.Local.FunctionsMetaplectic.Construction.Position F d where
  toAddEquiv := AddEquiv.neg _
  continuous_toFun := continuous_neg
  continuous_invFun := continuous_neg

def bruHatReflection {F : Type} [NormedField F] (d : ℕ) :
    Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat F d :=
  CoordinateChange.Construction.schwartzBruhat_coordinateEquiv (positionNegation d)

theorem fourierPhaseRotation_twice {F : Type} [AddGroup F] {d : ℕ} (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    FourierCovariance.Construction.fourierPhaseRotation (FourierCovariance.Construction.fourierPhaseRotation v) = -v := by
  funext i
  cases i <;> rfl

theorem reflection_heisenberg {F : Type} [Field F] {d : ℕ}
    (ψ : AddChar F ℂ) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Weil.Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    (fun x => Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f (-x)) =
      Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (-v) (fun x => f (-x)) := by
  funext x
  have hphase : (∑ i, v (Sum.inr i) * ((-x) i - v (Sum.inl i) / 2)) =
      ∑ i, (-v) (Sum.inr i) * (x i - (-v) (Sum.inl i) / 2) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.neg_apply, neg_div]
    ring
  have harg : (fun i => (-x) i - v (Sum.inl i)) =
      -(fun i => x i - (-v) (Sum.inl i)) := by
    funext i
    simp only [Pi.neg_apply]
    ring
  unfold Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction
  rw [hphase, harg]

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable [IsUltrametricDist F] [CharZero F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun t : F => ψ t)) (hunit : ∀ t, ‖ψ t‖ = 1)
variable (hnontrivial : ∃ t, ψ t ≠ 1)
variable (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure]

omit [CompleteSpace F] in
theorem ultraFourier_covariance (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial μ (UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f) =
      UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc (FourierCovariance.Construction.fourierPhaseRotation v)
        (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial μ f) := by
  apply Subtype.ext
  exact FourierCovariance.Construction.fourierIntegral_heisenberg ψ μ v f.val

omit [CompleteSpace F] [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] in
theorem bruHatReflection_covariance (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    bruHatReflection d (UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f) =
      UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc (-v) (bruHatReflection d f) := by
  apply Subtype.ext
  exact reflection_heisenberg ψ v f.val

theorem ultraFourier_square_scalar :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat F d,
      bruHatReflection d (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial μ
        (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial μ f)) = z • f := by
  let T := FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial μ
  let R := bruHatReflection (F := F) d
  let A : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := R.toLinearMap.comp (T.comp T)
  have hcomm (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
      A (UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f) = UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v (A f) := by
    change R (T (T (UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f))) =
      UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v (R (T (T f)))
    rw [ultraFourier_covariance, ultraFourier_covariance, fourierPhaseRotation_twice,
      bruHatReflection_covariance, neg_neg]
  obtain ⟨z, hz⟩ := UltraMultiplier.Construction.ultra_commutant_scalar hF ψ hc hnontrivial hunit A hcomm
  refine ⟨z, ?_, hz⟩
  intro hz0
  obtain ⟨u, hu⟩ := LocalTest.Construction.exists_test_nonzero F hF d
  have hTi := FourierUltra.Construction.ultraFourierLinearMap_injective hF ψ hc hunit hnontrivial μ
  have hAi : Function.Injective A := R.injective.comp (hTi.comp hTi)
  apply hu
  apply hAi
  rw [map_zero, hz, hz0, zero_smul]

theorem ultraFourierLinearMap_surjective :
    Function.Surjective (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial μ) := by
  obtain ⟨z, hz, hscalar⟩ := ultraFourier_square_scalar hF ψ hc hunit hnontrivial μ
  intro f
  let g := z⁻¹ • bruHatReflection d f
  refine ⟨FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial μ g, ?_⟩
  apply (bruHatReflection d).injective
  rw [hscalar]
  change z • (z⁻¹ • bruHatReflection d f) = bruHatReflection d f
  rw [smul_smul, mul_inv_cancel₀ hz, one_smul]

def ultraFourierEquiv : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat F d :=
  LinearEquiv.ofBijective (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial μ)
    ⟨FourierUltra.Construction.ultraFourierLinearMap_injective hF ψ hc hunit hnontrivial μ,
      ultraFourierLinearMap_surjective hF ψ hc hunit hnontrivial μ⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.FourierInvolution.Construction
