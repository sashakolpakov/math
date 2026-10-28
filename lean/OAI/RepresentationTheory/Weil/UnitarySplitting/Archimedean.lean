import OAI.RepresentationTheory.Weil.UnitarySplitting.RealFactorSplittings
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealFieldFrame

/-! # Archimedean -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Archimedean.Construction

noncomputable section

/-! The real dual-pair splitting in arbitrary archimedean field coordinates. -/

open _root_.Matrix

theorem archimedean_dual_pair_splitting
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] {m n : ℕ}
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K)
    (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2)
    (hne : ∃ z : E, σ z ≠ z)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (hn : ∃ x : F, ψ x ≠ 1) (characters : Characters.Construction.SplittingCharacters F E m n)
    (hH : DualPair.Construction.adjointMatrix σ H = H) (hK : DualPair.Construction.adjointMatrix σ K = -K)
    (hHdet : H.det ≠ 0) (hKdet : K.det ≠ 0)
    (e : ℝ ≃+* F) (he : Continuous e) (hei : Continuous e.symm) :
    ∃ splitting : (DualPair.Construction.unitaryGroup σ H × DualPair.Construction.unitaryGroup σ K) →ₜ* Oscillator.Construction.CircleExtension σ H K c ψ,
      ∀ g, Oscillator.Construction.circleProjection σ H K c ψ (splitting g) = DualPair.Construction.continuousDualPairAction σ H K g := by
  let : Algebra ℝ F := e.toRingHom.toAlgebra
  let eR : ℝ ≃ₐ[ℝ] F := { e with commutes' := fun _ => rfl }
  let : FiniteDimensional ℝ F := eR.toLinearEquiv.finiteDimensional
  let : Algebra ℝ E := ((algebraMap F E).comp e.toRingHom).toAlgebra
  let : IsScalarTower ℝ F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ F E
  have hdimF : Module.finrank ℝ F = 1 := eR.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self ℝ)
  have hdimE : Module.finrank ℝ E = 2 := by
    rw [← Module.finrank_mul_finrank ℝ F E, hdimF, hQuadratic, one_mul]
  let σR := σ.restrictScalars ℝ
  let cR := RealFieldFrame.Construction.realFieldSymplecticFrame eR σ H K c
  let χ := ψ.compAddMonoidHom e.toAddEquiv.toAddMonoidHom
  have hχn : ∃ t, χ t ≠ 1 := by
    obtain ⟨x, hx⟩ := hn
    refine ⟨e.symm x, ?_⟩
    change ψ (e (e.symm x)) ≠ 1
    rwa [e.apply_symm_apply]
  obtain ⟨sR, hsR⟩ := RealFactorSplittings.Construction.real_dual_pair_splitting σR H K cR hE (hEmbedding.comp he) hdimE hne
    χ (hc.comp he) (fun t => hu (e t)) hχn (RealFieldFrame.Construction.realFieldSplittingCharacters eR he characters)
    hH hK hHdet hKdet
  apply CircleFieldTransport.Construction.realField_splitting_transport σ σR H K c cR hF e he hei ψ hc hu
    (RealFieldFrame.Construction.realFieldSymplecticFrame_coordinates eR he hei σ H K c) (DualPair.Construction.continuousDualPairAction σ H K) sR
  intro g v
  have hh := congrArg (fun a : Oscillator.Construction.TensorSymplectic σR H K => a.val v) (hsR g)
  exact hh

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Archimedean.Construction
