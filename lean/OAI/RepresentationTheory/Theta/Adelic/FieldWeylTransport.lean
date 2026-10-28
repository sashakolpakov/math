import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylCoefficientTransport
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.FieldCoordinates
import OAI.RepresentationTheory.Weil.Local.FieldFourier

/-! # Field Weyl Transport -/

namespace OAI.RepresentationTheory.Theta.Adelic.FieldWeylTransport

noncomputable section

/-! Exact field transport of Weyl matrix coefficients and their weak
Gaussian integrals, including positive rescaling of position measure. -/

open _root_.MeasureTheory
open scoped NNReal

open OAI.RepresentationTheory.Weil.Local.FieldFourier.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.WeylCoefficientTransport.Construction

variable {k l : Type} [NormedField k] [NormedField l]
variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
variable [SecondCountableTopology k] [SecondCountableTopology l]
variable (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) (N : ℕ) (ψ : AddChar k ℂ)

theorem weylMatrixCoefficient_field
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k N)) (f h : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (μ.map (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N))
      (f ∘ (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm) (h ∘ (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm)
      (fun i => e (v i)) = Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f h v := by
  let p := Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N
  change (∫ x, Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (fun i => e (v i))
      (f ∘ p.symm) x * star ((h ∘ p.symm) x) ∂μ.map p.toHomeomorph.toMeasurableEquiv) = _
  rw [integral_map_equiv]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (ψ (e.symm (∑ i, e (v (.inr i)) * (e (x i) - e (v (.inl i)) / 2))) *
      f (fun i => e.symm (e (x i) - e (v (.inl i))))) * star (h (fun i => e.symm (e (x i)))) =
      (ψ (∑ i, v (.inr i) * (x i - v (.inl i) / 2)) * f (fun i => x i - v (.inl i))) * star (h x)
    simp only [map_sum, map_mul, map_sub, map_div₀, map_ofNat, e.symm_apply_apply]

theorem weakWeylGaussian_field
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k N)) (ν : Measure (Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N))
    (q : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N → k) (q' : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace l N → l)
    (hq : ∀ v, q' (fun i => e (v i)) = e (q v)) (f h : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ) :
    Weil.UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (μ.map (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N))
      (ν.map (Weil.UnitarySplitting.FieldCoordinates.Construction.coordinateFieldEquiv (Fin N ⊕ Fin N) e he hi)) q'
      (f ∘ (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm) (h ∘ (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm) =
        Weil.UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian ψ μ ν q f h := by
  let p := Weil.UnitarySplitting.FieldCoordinates.Construction.coordinateFieldEquiv (Fin N ⊕ Fin N) e he hi
  unfold Weil.UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian
  change (∫ v, Weil.Local.FieldFourier.Construction.fieldCharacter e ψ (q' v) *
    Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (μ.map (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N))
      (f ∘ (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm) (h ∘ (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm) v
      ∂ν.map p.toHomeomorph.toMeasurableEquiv) = _
  rw [integral_map_equiv]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    change Weil.Local.FieldFourier.Construction.fieldCharacter e ψ (q' (fun i => e (v i))) *
      Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (μ.map (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N))
        (f ∘ (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm) (h ∘ (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm)
        (fun i => e (v i)) = _
    rw [hq, weylMatrixCoefficient_field]
    change ψ (e.symm (e (q v))) * _ = ψ (q v) * _
    rw [e.symm_apply_apply]

omit [BorelSpace k] [SecondCountableTopology k] in
theorem weakWeylGaussian_smul_position
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k N)) (ν : Measure (Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) (a : ℝ≥0)
    (q : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N → k) (f h : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ) :
    Weil.UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian ψ (a • μ) ν q f h = (a : ℂ) * Weil.UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian ψ μ ν q f h := by
  unfold Weil.UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  simp_rw [mul_left_comm (ψ _) (a : ℂ)]
  rw [integral_const_mul]

end

end OAI.RepresentationTheory.Theta.Adelic.FieldWeylTransport
