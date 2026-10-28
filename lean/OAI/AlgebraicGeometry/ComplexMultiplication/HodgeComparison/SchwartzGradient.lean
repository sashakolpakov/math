import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanGradient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential

/-! # Schwartz Gradient -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SchwartzGradient.CM.Construction

noncomputable section

/-! The ordinary gradient of a Schwartz function and its exact relation to
the normalized Sobolev gradient used in the local weak equation. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap LineDeriv

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι]

def schwartzOrdinaryGradient (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (x : E) : EuclideanSpace ℂ ι :=
  ∑ i, (∂_{b i} g : 𝓢(E, ℂ)) x • EuclideanSpace.basisFun ι ℂ i

theorem schwartzOrdinaryGradient_apply (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (x : E) (i : ι) : schwartzOrdinaryGradient b g x i = (∂_{b i} g : 𝓢(E, ℂ)) x := by
  classical
  simp [schwartzOrdinaryGradient, EuclideanSpace.basisFun_apply, Pi.single_apply]

theorem schwartzOrdinaryGradient_zero (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    {x : E} (hx : x ∉ tsupport g) : schwartzOrdinaryGradient b g x = 0 := by
  apply PiLp.ext
  intro i
  rw [schwartzOrdinaryGradient_apply]
  exact image_eq_zero_of_notMem_tsupport (fun h => hx (SchwartzMap.tsupport_lineDerivOp_subset (b i) g h))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem sobolevVectorGradient_schwartz_normalization (b : OrthonormalBasis ι ℝ E)
    (g : 𝓢(E, ℂ)) :
    ∀ᵐ x ∂(volume : Measure E),
      (2 * Real.pi * Complex.I : ℂ) • EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 g) x =
        schwartzOrdinaryGradient b g x := by
  let u := SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 g
  have hc : ∀ᵐ x ∂(volume : Measure E), ∀ i : ι,
      (2 * Real.pi * Complex.I : ℂ) • FourierEnergy.CM.Construction.sobolevNormalizedGradient b u i x =
        (∂_{b i} g : 𝓢(E, ℂ)) x := by
    apply ae_all_iff.mpr
    intro i
    have hD : SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) u = (∂_{b i} g : 𝓢(E, ℂ)).toLp 2 :=
      SobolevDifferential.CM.Construction.sobolevL2Derivative_schwartz (b i) g
    have hκ := FourierEnergy.CM.Construction.sobolevNormalizedGradient_derivative b u i
    rw [hD] at hκ
    filter_upwards [Lp.coeFn_smul (2 * Real.pi * Complex.I : ℂ) (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u i),
      (∂_{b i} g : 𝓢(E, ℂ)).coeFn_toLp 2] with x hx hgx
    rw [← hκ] at hx
    exact hx.symm.trans hgx
  filter_upwards [LpComponents.CM.Construction.lpOrthonormalSynthesis_coe (EuclideanSpace.basisFun ι ℂ)
    (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u), hc] with x hx hc
  change (2 * Real.pi * Complex.I : ℂ) •
    LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u) x = _
  rw [hx, Finset.smul_sum]
  unfold schwartzOrdinaryGradient
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ((2 * Real.pi * Complex.I : ℂ) • FourierEnergy.CM.Construction.sobolevNormalizedGradient b u i x) •
        EuclideanSpace.basisFun ι ℂ i :=
      smul_smul (2 * Real.pi * Complex.I : ℂ) (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u i x) _
    _ = _ := congrArg (fun a : ℂ => a • EuclideanSpace.basisFun ι ℂ i) (hc i)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SchwartzGradient.CM.Construction
