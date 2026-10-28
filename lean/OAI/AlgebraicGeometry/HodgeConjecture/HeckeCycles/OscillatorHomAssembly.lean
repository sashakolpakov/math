import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticCoordinateLemmas

/-! # Oscillator Hom Assembly -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorHomAssembly.CM

noncomputable section

/-! Assemble a genuine oscillator homomorphism from proved covariance
and Haar unitarity, explicitly reconciling finite-index equality instances. -/

open scoped Classical _root_.Matrix

variable {I G : Type*} [Fintype I] [DecidableEq I] [Group G]
  (s : G →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (T : G →* (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I))
  (hu : ∀ g f h, Finite.FiniteOscillator.CM.integralPairing (T g f) (T g h) =
    Finite.FiniteOscillator.CM.integralPairing f h)
  (hc : ∀ g v f, T g (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) f) =
    Finite.FourierHeisenberg.CM.operator (fun i => ((s g).val *ᵥ v) (.inl i))
      (fun i => ((s g).val *ᵥ v) (.inr i)) (T g f))

def canonicalProjection : G →* @RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I _ (Classical.decEq I) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf _ :=
  (@RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf _ _ inferInstance (Classical.decEq I) _ (Equiv.refl I)).comp s

theorem canonical_matrix (g : G) : (canonicalProjection s g).val = (s g).val :=
  SymplecticCoordinateLemmas.CM.reindex_refl_matrix inferInstance (Classical.decEq I) (s g)

include hc in
theorem graph_covariance (g : G) (v : Finite.FiniteOscillator.CM.Phase (I := I)) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    Finite.FiniteOscillator.CM.graph v f h ↔
      Finite.FiniteOscillator.CM.graph (Finite.FiniteOscillator.CM.phaseAction (canonicalProjection s g) v)
        (T g f) (T g h) := by
  rw [Finite.ReindexHeisenberg.CM.graph_eq, Finite.ReindexHeisenberg.CM.graph_eq]
  change h = Finite.FourierHeisenberg.CM.operator _ _ f ↔ T g h =
    Finite.FourierHeisenberg.CM.operator (fun i => ((canonicalProjection s g).val *ᵥ v) (.inl i))
      (fun i => ((canonicalProjection s g).val *ᵥ v) (.inr i)) (T g f)
  rw [canonical_matrix, ← hc]
  exact (T g).injective.eq_iff.symm

def lift : G →* Finite.FiniteOscillator.CM.Oscillator (I := I) where
  toFun g := ⟨(canonicalProjection s g, T g), hu g, graph_covariance s T hc g⟩
  map_one' := Subtype.ext (Prod.ext (canonicalProjection s).map_one T.map_one)
  map_mul' g h := Subtype.ext (Prod.ext ((canonicalProjection s).map_mul g h) (T.map_mul g h))

theorem projection_matrix (g : G) : (Finite.FiniteOscillator.CM.projection (lift s T hu hc g)).val = (s g).val :=
  canonical_matrix s g

theorem action (g : G) : Finite.FiniteOscillator.CM.action (lift s T hu hc g) = T g := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorHomAssembly.CM
