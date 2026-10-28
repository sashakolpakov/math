import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCompositionPhase
import OAI.RepresentationTheory.Weil.UnitarySplitting.StandardTransvections

/-! # Weak Cayley Coefficients -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeakCayleyCoefficients.Construction

noncomputable section

section

/-! The weak Cayley Gaussian has the exact Weyl intertwining relation. -/

open _root_.MeasureTheory _root_.Topology Filter

theorem weakCayleyGaussian_intertwines
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic F d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (hD : ∀ x, D x = g.val x - x)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν
        (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D)
        (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f).val h.val =
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν
        (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D)
        f.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (-g.val w) h).val := by
  let β := StandardTransvections.Construction.standardSymplecticBilinear F d
  let q := CayleyCompositionPhase.Construction.cayleyWeylPhase β D
  let C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val h.val
  have hAlt : ∀ x, β x x = 0 := StandardTransvections.Construction.standardSymplecticBilinear_alternating d
  have hphase (u : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
      q (u - w) + β u w / 2 = q (u - g.val w) + β (g.val w) u / 2 :=
    CayleyCompositionPhase.Construction.cayleyWeylPhase_translation β hAlt g.val D g.property hD u w
  have hleft (u : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
      Oscillator.Construction.standardSymplecticPairing d (u - w) w = β u w := by
    change β (u - w) w = β u w
    simp only [map_sub, LinearMap.sub_apply, hAlt, sub_zero]
  have hright (u : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
      Oscillator.Construction.standardSymplecticPairing d (g.val w) (u - g.val w) = β (g.val w) u := by
    change β (g.val w) (u - g.val w) = β (g.val w) u
    simp only [map_sub, hAlt, sub_zero]
  calc
    _ = ∫ u, ψ (q (u - w) + β u w / 2) * C u ∂ν := by
      unfold WeakWeylGaussian.Construction.weakWeylGaussian
      rw [← integral_sub_right_eq_self
        (fun v => ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
          (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f).val h.val v) w]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        dsimp only
        rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_input_shift hF ψ hc hu, sub_add_cancel, hleft,
          ψ.map_add_eq_mul, mul_assoc]
    _ = ∫ u, ψ (q (u - g.val w) + β (g.val w) u / 2) * C u ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        dsimp only
        rw [hphase]
    _ = _ := by
      unfold WeakWeylGaussian.Construction.weakWeylGaussian
      rw [← integral_sub_right_eq_self
        (fun v => ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
          f.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (-g.val w) h).val v) (g.val w)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        dsimp only
        rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_output_shift hF ψ hc hu, neg_neg]
        have huadd : g.val w + (u - g.val w) = u := by abel
        rw [huadd, hright, ψ.map_add_eq_mul, mul_assoc]

end

/-! Coherent coefficients of the weak Cayley form are full Fourier
transforms, multiplied by the Cayley quadratic phase. -/

open _root_.MeasureTheory

theorem weakCayleyGaussian_output_coefficient
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic F d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (hD : ∀ x, D x = g.val x - x)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν
        (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D)
        f.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v h).val =
      ψ (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D v) *
        ∫ x, ψ (StandardTransvections.Construction.standardSymplecticBilinear F d (D.symm v) x) *
          (ψ (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D x) *
            WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val h.val x) ∂ν := by
  let β := StandardTransvections.Construction.standardSymplecticBilinear F d
  let q := CayleyCompositionPhase.Construction.cayleyWeylPhase β D
  have hAlt : ∀ x, β x x = 0 := StandardTransvections.Construction.standardSymplecticBilinear_alternating d
  have hp (x : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : q (x + v) + β (-v) (x + v) / 2 =
      q x + q v + β (D.symm v) x :=
    CayleyCompositionPhase.Construction.cayleyWeylPhase_output_shift β hAlt g.val D g.property hD x v
  unfold WeakWeylGaussian.Construction.weakWeylGaussian
  rw [← integral_add_right_eq_self
    (fun x => ψ (q x) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
      f.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v h).val x) v,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_output_shift hF ψ hc hu]
    have hx : -v + (x + v) = x := by abel
    rw [hx, ← mul_assoc, ← ψ.map_add_eq_mul]
    change ψ (q (x + v) + β (-v) (x + v) / 2) * _ = _
    rw [hp, ψ.map_add_eq_mul, ψ.map_add_eq_mul]
    ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeakCayleyCoefficients.Construction
