import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyMatrixCoefficient
import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticGaussianRegularization

/-! # Real Cayley Composition -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyComposition.Construction

noncomputable section

/-! The composition scalar of actual Cayley operators is the regularized
Gaussian of the sum of their quadratic phases. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

theorem realCayleyOperator_composition
    {d : ℕ} (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun x : ℝ => ψ x)) (hu : ∀ x : ℝ, ‖ψ x‖ = 1)
    (hn : ∃ x : ℝ, ψ x ≠ 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (g h : FrameTransport.Construction.StandardSymplectic ℝ d)
    (Dg Dh Dgh : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)
    (hDg : ∀ x, Dg x = g.val x - x) (hDh : ∀ x, Dh x = h.val x - x)
    (hDgh : ∀ x, Dgh x = (g * h).val x - x)
    (Γ : ℂ) (hΓ : QuadraticGaussianRegularization.Construction.HasGaussianRegularization ν ψ
      (fun x => CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) Dg x +
        CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) Dh x) Γ)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g Dg hDg
      (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν h Dh hDh f) =
        Γ • RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν (g * h) Dgh hDgh f := by
  let β := StandardTransvections.Construction.standardSymplecticBilinear ℝ d
  let qg := CayleyCompositionPhase.Construction.cayleyWeylPhase β Dg
  let qh := CayleyCompositionPhase.Construction.cayleyWeylPhase β Dh
  let qgh := CayleyCompositionPhase.Construction.cayleyWeylPhase β Dgh
  let Q : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℝ := fun x => qg x + qh x
  let B := CayleyCompositionPhase.Construction.cayleySumForm β Dg Dh
  let L : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d := fun x => -CayleyCompositionPhase.Construction.cayleyCompositionShift h.val Dg Dgh x
  have hqc : Continuous qh := CayleySynthesisPairing.Construction.standardCayleyWeylPhase_continuous RealFourierUnitary.Construction.real_nondiscrete Dh
  have hLc : Continuous L := by
    change Continuous (fun x => -(CayleyCompositionPhase.Construction.cayleyCompositionShift h.val Dg Dgh).toContinuousLinearEquiv x)
    fun_prop
  have hadd : ∀ v x, Q (v + x) = Q v + Q x + B v x := CayleyCompositionPhase.Construction.cayleySumForm_polar β
    (StandardTransvections.Construction.standardSymplecticBilinear_alternating d) g.val h.val Dg Dh g.property h.property hDg hDh
  have hfreq (v x : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) : B v (L x) = β (-(Dh.symm v)) x :=
    CayleyCompositionPhase.Construction.cayleySumForm_composition_frequency g.val h.val Dg Dh Dgh hDg hDh hDgh β
      (StandardTransvections.Construction.standardSymplecticBilinear_alternating d) g.property h.property v x
  have hphase (x : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) : -Q (L x) + qh x = qgh x := by
    have hh := CayleyCompositionPhase.Construction.cayleyComposition_residual_phase g.val h.val Dg Dh Dgh hDg hDh hDgh β
      (StandardTransvections.Construction.standardSymplecticBilinear_alternating d) g.property h.property x
    change -(qg (L x) + qh (L x)) + qh x = qgh x
    change qh x - (qg (L x) + qh (L x)) = qgh x at hh
    linear_combination hh
  apply UltraCayleyOperator.Construction.testPairing_ext
  intro k
  let C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d) f.val k.val
  let φ : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℂ := fun x => ψ (qh x) * C x
  let T : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℂ := fun v => ∫ x, ψ (B v (L x)) * φ x ∂ν
  have hCc : Continuous C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient_continuous ψ hc hu (Weak.Construction.referencePositionMeasure ℝ d) f k
  have hφc : Continuous φ := (hc.comp hqc).mul hCc
  have hφi : Integrable φ ν := RealWeakGaussian.Construction.weakWeylGaussian_integrable_real ψ hc hu hn ν
    (Weak.Construction.referencePositionMeasure ℝ d) qh hqc f k
  have hcoef (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) :
      WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d)
        (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν h Dh hDh f).val k.val v = ψ (qh v) * T v := by
    rw [RealCayleyMatrixCoefficient.Construction.realCayleyOperator_matrixCoefficient]
    dsimp only [T]
    simp_rw [hfreq]
    rfl
  have heq : T = fun v => ψ (-qh v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d)
      (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν h Dh hDh f).val k.val v := by
    funext v
    rw [hcoef, ← mul_assoc, ← ψ.map_add_eq_mul, neg_add_cancel, ψ.map_zero_eq_one, one_mul]
  have hTc : Continuous T := by
    rw [heq]
    exact (hc.comp hqc.neg).mul (WeylMatrixCoefficients.Construction.weylMatrixCoefficient_continuous ψ hc hu
      (Weak.Construction.referencePositionMeasure ℝ d) (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν h Dh hDh f) k)
  have hTi : Integrable T ν := by
    rw [heq]
    exact RealWeakGaussian.Construction.weakWeylGaussian_integrable_real ψ hc hu hn ν (Weak.Construction.referencePositionMeasure ℝ d)
      (fun v => -qh v) hqc.neg (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν h Dh hDh f) k
  rw [map_smul, inner_smul_right, RealCayleyOperator.Construction.realCayleyOperator_pairing, RealCayleyOperator.Construction.realCayleyOperator_pairing]
  change (∫ v, ψ (qg v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d)
    (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν h Dh hDh f).val k.val v ∂ν) =
      Γ * ∫ x, ψ (qgh x) * C x ∂ν
  simp_rw [hcoef, ← mul_assoc, ← ψ.map_add_eq_mul]
  have hGF := hΓ.fourier_pairing_comp (fun x y => B x y) hadd L hLc φ hφc hφi hTc hTi
  change (∫ v, ψ (Q v) * T v ∂ν) = _
  rw [hGF]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change ψ (-Q (L x)) * (ψ (qh x) * C x) = ψ (qgh x) * C x
    rw [← mul_assoc, ← ψ.map_add_eq_mul, hphase]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyComposition.Construction
