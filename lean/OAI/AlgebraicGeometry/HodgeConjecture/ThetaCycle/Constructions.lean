import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteCMWedgeProduct
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMWedgeAlbanese

/-! # Constructions -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Constructions

noncomputable section

/-!
# ThetaCycle: the full conditional non-elementary switch

The conclusion is the accepted native surface statement, including its
arithmetic uniformization, four algebraic maps, nonzero id,id,c,c product,
and arbitrarily deep principal refinements with the integral degree law.

Only full named prerequisites remain explicit. Full native ThetaKernel is applied
with full AdelicTheta, and the native HodgeComparison theorem supplies the Albanese comparison.
The construction retains one original total finite Schwartz input through
the actual smooth approximation, full PairingContinuity persistence, finite theta-wedge
factorizations, and full HeckeCycles source-family extraction at a common level.
No geometric existence, compatibility, or nonvanishing premise is added.
The accepted statement specification is not imported.
-/

open _root_.CategoryTheory
open OAI.RepresentationTheory.Theta.Adelic.Data

/-- The full native ThetaCycle conclusion, conditional on the full named
prerequisite propositions. All surface and theta data are constructed. -/
theorem four_abelian_maps_nonzero_product
    (hReferenceFamily : Moduli.CM.ReferenceFamilyInput) (hAdelicTheta : RepresentationTheory.Theta.Adelic.Data.CompleteStatement)
    (hHeckeCycles : HeckeCycles.CM.HeckeCyclesInput) (hPairingContinuity : Persistence.CM.PairingContinuityInput.{0, 0, 0})
    (hDegreeTwo : Albanese.CM.ConditionalWeightOneInput) (hHolomorphicAlgebraicity : DegreeTwo.Transport.Constructions.HolomorphicAlgebraicityInput) (hConstruction : DegreeTwo.Transport.Constructions.ConstructionInput)
    (K : IntermediateField ℚ ℂ)
    [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (hbalance : ∀ τ : Gal(K/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
      ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (hid : ∀ i, (v i).val 1 = true)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)))
    (Nbase : ℕ) (hNbase : 0 < Nbase) :
    ∃ (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ)
      (S : Cm.PrincipalBallSurface K B N)
      (f : (i : Fin 4) →
        S.surface.variety.toOver ⟶ (R i).abelianVariety.toOver),
      0 < N ∧ Nbase ∣ N ∧
      S.surface.evaluate (Cm.fourClass K v R S.surface.variety f) ≠ 0 ∧
      ∀ L : ℕ, 0 < L →
        ∃ (M : ℕ) (T : Cm.PrincipalBallSurface K B M)
          (p : Cm.PrincipalRefinement K S T),
          0 < M ∧ L ∣ M ∧
          T.surface.evaluate
              (Cm.fourClass K v R T.surface.variety (fun i => p.map ≫ f i)) =
            (p.degree : ℂ) *
              S.surface.evaluate (Cm.fourClass K v R S.surface.variety f) ∧
          T.surface.evaluate
            (Cm.fourClass K v R T.surface.variety (fun i => p.map ≫ f i)) ≠ 0 := by
  obtain ⟨D, ⟨T₀⟩⟩ := InitialSetup.CM.exists_initial_surface_theta_setup K hReferenceFamily v hbalance hid hother Nbase hNbase
  obtain ⟨N, hN, hDN, hprod⟩ :=
    ConcreteCMWedgeProduct.CM.exists_actual_principal_cm_wedge_product K D T₀ hid hAdelicTheta hPairingContinuity hHeckeCycles
  let S := D.surface N hN hDN
  obtain ⟨f, hf⟩ := CMWedgeAlbanese.CM.cm_wedge_product_algebraic_maps hDegreeTwo hHolomorphicAlgebraicity hConstruction K v R S.surface hprod
  refine ⟨D.ball, N, S, f, hN, D.base_divides.trans hDN, hf, ?_⟩
  intro L hL
  let M := N * L
  have hM : 0 < M := Nat.mul_pos hN hL
  have hNM : N ∣ M := dvd_mul_right _ _
  have hDM : D.depth ∣ M := hDN.trans hNM
  let T := D.surface M hM hDM
  obtain ⟨p⟩ := PeriodTotal.CM.setup_principal_refinement K D N M hN hM hDN hDM hNM
  exact ⟨M, T, p, hM, dvd_mul_left _ _, Betti.CM.fourClass_evaluate_pullback K v R p f,
    Betti.CM.fourClass_evaluate_pullback_ne_zero K v R p f hf⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Constructions
