import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyMatrixCoefficient
import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianCutoff

/-! # Ultra Cayley Composition -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyComposition.Construction

noncomputable section

/-! The composition scalar of actual Cayley operators is the stable
Gaussian of the sum of their quadratic phases. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

theorem ultraCayleyOperator_composition
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [IsUltrametricDist F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (hn : ∃ x : F, ψ x ≠ 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (g h : FrameTransport.Construction.StandardSymplectic F d)
    (Dg Dh Dgh : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (hDg : ∀ x, Dg x = g.val x - x) (hDh : ∀ x, Dh x = h.val x - x)
    (hDgh : ∀ x, Dgh x = (g * h).val x - x)
    (Γ : ℂ) (hΓ : GaussianCutoff.Construction.HasGaussianCutoffs ν ψ
      (fun x => CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) Dg x +
        CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) Dh x) Γ)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν g Dg hDg
      (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν h Dh hDh f) =
        Γ • UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν (g * h) Dgh hDgh f := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let β := StandardTransvections.Construction.standardSymplecticBilinear F d
    let qg := CayleyCompositionPhase.Construction.cayleyWeylPhase β Dg
    let qh := CayleyCompositionPhase.Construction.cayleyWeylPhase β Dh
    let qgh := CayleyCompositionPhase.Construction.cayleyWeylPhase β Dgh
    let Q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F := fun x => qg x + qh x
    let B := CayleyCompositionPhase.Construction.cayleySumForm β Dg Dh
    let L : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → Local.FunctionsMetaplectic.Construction.PhaseSpace F d := fun x => -CayleyCompositionPhase.Construction.cayleyCompositionShift h.val Dg Dgh x
    have hqc : Continuous qh := CayleySynthesisPairing.Construction.standardCayleyWeylPhase_continuous hF Dh
    have hQc : Continuous Q := (CayleySynthesisPairing.Construction.standardCayleyWeylPhase_continuous hF Dg).add hqc
    have hBc : Continuous (fun p : Local.FunctionsMetaplectic.Construction.PhaseSpace F d × Local.FunctionsMetaplectic.Construction.PhaseSpace F d => B p.1 p.2) := by
      change Continuous (fun p : Local.FunctionsMetaplectic.Construction.PhaseSpace F d × Local.FunctionsMetaplectic.Construction.PhaseSpace F d => BilinearFourierCoordinates.Construction.finiteBilinearContinuous B p.1 p.2)
      fun_prop
    have hLc : Continuous L := by
      change Continuous (fun x => -(CayleyCompositionPhase.Construction.cayleyCompositionShift h.val Dg Dgh).toContinuousLinearEquiv x)
      fun_prop
    have hBs : ∀ x y, B x y = B y x := CayleyCompositionPhase.Construction.cayleySumForm_symmetric β
      (StandardTransvections.Construction.standardSymplecticBilinear_alternating d) g.val h.val Dg Dh g.property h.property hDg hDh
    have hadd : ∀ v x, Q (v + x) = Q v + Q x + B v x := CayleyCompositionPhase.Construction.cayleySumForm_polar β
      (StandardTransvections.Construction.standardSymplecticBilinear_alternating d) g.val h.val Dg Dh g.property h.property hDg hDh
    have hfreq (v x : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : B v (L x) = β (-(Dh.symm v)) x :=
      CayleyCompositionPhase.Construction.cayleySumForm_composition_frequency g.val h.val Dg Dh Dgh hDg hDh hDgh β
        (StandardTransvections.Construction.standardSymplecticBilinear_alternating d) g.property h.property v x
    have hphase (x : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : -Q (L x) + qh x = qgh x := by
      have hh := CayleyCompositionPhase.Construction.cayleyComposition_residual_phase g.val h.val Dg Dh Dgh hDg hDh hDgh β
        (StandardTransvections.Construction.standardSymplecticBilinear_alternating d) g.property h.property x
      change -(qg (L x) + qh (L x)) + qh x = qgh x
      change qh x - (qg (L x) + qh (L x)) = qgh x at hh
      linear_combination hh
    apply UltraCayleyOperator.Construction.testPairing_ext
    intro k
    let C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val k.val
    let φ : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ := fun x => ψ (qh x) * C x
    let T : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ := fun v => ∫ x, ψ (B v (L x)) * φ x ∂ν
    have hCc : Continuous C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient_continuous ψ hc hu (Weak.Construction.referencePositionMeasure F d) f k
    have hCs : HasCompactSupport C := WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hF ψ hn
      (Weak.Construction.referencePositionMeasure F d) f k
    have hφc : Continuous φ := (hc.comp hqc).mul hCc
    have hφs : HasCompactSupport φ := hCs.mul_left
    have hcoef (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
        WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
          (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν h Dh hDh f).val k.val v = ψ (qh v) * T v := by
      rw [UltraCayleyMatrixCoefficient.Construction.ultraCayleyOperator_matrixCoefficient]
      dsimp only [T]
      simp_rw [hfreq]
      rfl
    have hTs : HasCompactSupport T := by
      have heq : T = fun v => ψ (-qh v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
          (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν h Dh hDh f).val k.val v := by
        funext v
        rw [hcoef, ← mul_assoc, ← ψ.map_add_eq_mul, neg_add_cancel, ψ.map_zero_eq_one, one_mul]
      rw [heq]
      exact (WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hF ψ hn (Weak.Construction.referencePositionMeasure F d)
        (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν h Dh hDh f) k).mul_left
    rw [map_smul, inner_smul_right, UltraCayleyOperator.Construction.ultraCayleyOperator_pairing, UltraCayleyOperator.Construction.ultraCayleyOperator_pairing]
    change (∫ v, ψ (qg v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
      (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν h Dh hDh f).val k.val v ∂ν) =
        Γ * ∫ x, ψ (qgh x) * C x ∂ν
    simp_rw [hcoef, ← mul_assoc, ← ψ.map_add_eq_mul]
    have hGF := GaussianCutoff.Construction.gaussianCutoff_fourier_pairing_comp ψ hc hu ν Q hQc (fun x y => B x y) hBc hBs hadd Γ hΓ
      L hLc φ hφc hφs hTs
    change (∫ v, ψ (Q v) * T v ∂ν) = _
    rw [hGF]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ψ (-Q (L x)) * (ψ (qh x) * C x) = ψ (qgh x) * C x
      rw [← mul_assoc, ← ψ.map_add_eq_mul, hphase]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyComposition.Construction
