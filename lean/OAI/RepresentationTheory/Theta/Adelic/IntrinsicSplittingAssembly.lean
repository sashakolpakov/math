import OAI.RepresentationTheory.Theta.Adelic.IntrinsicLeftFactor
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicRightFactor
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicCoverTopology

/-! # Intrinsic Splitting Assembly -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicSplittingAssembly.Intrinsic

noncomputable section

/-! Assembly of the two native oscillator lifts, with exact restrictions
to both factors retained for the normalization formulas. -/

open OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates

theorem native_splitting_assembly
    {k E : Type} [NormedField k] [NormedField E] [Algebra k E]
    [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n m : ℕ}
    (σ : E ≃ₐ[k] E) (H : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin m) (Fin m) E)
    (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar k ℂ)
    (s : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ H →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ)
    (t : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ K →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ)
    (hs : ∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ (s g) =
      CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.DualPair.Construction.dualPairAction σ H K (g, 1)))
    (ht : ∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ (t g) =
      CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.DualPair.Construction.dualPairAction σ H K (1, g)))
    (hcentral : ∀ b : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ,
      (∀ g, Commute (CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.DualPair.Construction.dualPairAction σ H K (g, 1)))
        (Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ b)) → ∀ g, Commute (s g) b) :
    ∃ S : (Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ H × Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ K) →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ,
      (∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ (S g) =
        CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.DualPair.Construction.dualPairAction σ H K g)) ∧
      (∀ g, S (g, 1) = s g) ∧ (∀ g, S (1, g) = t g) := by
  let : IsTopologicalGroup (Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ) :=
    IntrinsicCoverTopology.Intrinsic.localCover_isTopologicalGroup k (n * m) ψ
  have hcomm : ∀ g h, Commute (s g) (t h) := by
    intro g h
    apply hcentral (t h) _ g
    intro j
    rw [ht]
    exact (Weil.UnitarySplitting.Assembly.Construction.dualPair_factors_commute σ H K j h).map (CircleCoordinates.coordinateSymplectic σ H K c)
  refine ⟨Weil.UnitarySplitting.Assembly.Construction.commutingProductHom s t hcomm, ?_, ?_, ?_⟩
  · intro g
    change Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ (s g.1 * t g.2) = _
    rw [map_mul, hs, ht, ← map_mul, ← map_mul]
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
  · intro g
    change s g * t 1 = s g
    rw [map_one, mul_one]
  · intro g
    change s 1 * t g = t g
    rw [map_one, one_mul]

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicSplittingAssembly.Intrinsic
