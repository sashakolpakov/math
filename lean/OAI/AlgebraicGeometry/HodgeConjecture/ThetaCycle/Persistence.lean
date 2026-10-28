import OAI.Analysis.HodgeTheory.PairingContinuity

/-! # Persistence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Persistence.CM

noncomputable section

/-! The full PairingContinuity proposition, pinned at
cca2c4fa0a7cf63c05a0bf23dff2c6dbe4c1dacd, with its actual manifold forms and
all convergence, integral-continuity, and nonzero self-pairing premises. -/

open scoped _root_.Manifold ContDiff _root_.Topology
open OAI.Analysis.HodgeTheory.PairingContinuity

def PairingContinuityInput : Prop :=
  ∀ {X Φ RationalSplitting : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace (Fin 2 → ℂ) X]
    [IsManifold 𝓘(ℂ, Fin 2 → ℂ) ∞ X]
    (smoothTopology : TopologicalSpace (Analysis.HodgeTheory.PairingContinuity.SurfaceTwoForm X))
    (theta : Φ → RationalSplitting → Analysis.HodgeTheory.PairingContinuity.SurfaceTwoForm X)
    (pairing : Analysis.HodgeTheory.PairingContinuity.SurfaceTwoForm X → Analysis.HodgeTheory.PairingContinuity.SurfaceTwoForm X → ℂ)
    (φ : Φ)
    (s₀ : RationalSplitting)
    (admissible : RationalSplitting → Prop)
    (s : ℕ → RationalSplitting)
    (_h_admissible : ∀ n, admissible (s n))
    (_h_converges :
      letI := smoothTopology
      Filter.Tendsto (fun n => theta φ (s n))
        Filter.atTop (𝓝 (theta φ s₀)))
    (_h_pairing_continuous :
      letI := smoothTopology
      ContinuousAt (fun η => pairing (theta φ s₀) η)
        (theta φ s₀))
    (_h_self : pairing (theta φ s₀) (theta φ s₀) ≠ 0),
    ∃ s' : RationalSplitting,
      admissible s' ∧
      pairing (theta φ s₀) (theta φ s') ≠ 0

theorem nativePairingContinuityInput : PairingContinuityInput :=
  Analysis.HodgeTheory.PairingContinuity.persistence_of_nonzero_top_form_pairing

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Persistence.CM
