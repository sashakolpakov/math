import Mathlib
import OAI.Analysis.DifferentialForms.Manifold.Algebra
import OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree
import OAI.Analysis.DifferentialForms.Manifold.Derivative
import OAI.Analysis.DifferentialForms.Coordinates

/-! # Pairing Continuity -/

namespace OAI.Analysis.HodgeTheory.PairingContinuity

/-!
# PairingContinuity: persistence of a nonzero top-form pairing

The first theorem has exactly the hypotheses and conclusion of the committed
PairingContinuity specification. It uses no statement stubs. The supplied topology and
pairing retain their intended meanings: C∞ convergence of forms on the fixed
compact quotient, and the integral of the first form wedged with the conjugate
of the second. Their geometric construction is not an assertion of this file.

The second part connects the prerequisite outputs, with named hypotheses:
* `h_LocalApproximation` is the approximation conclusion of LocalApproximation, using its actual period
 coordinates. `NewSignsSplitting` groups the first four conjuncts in the output.
* `h_ThetaKernel_continuous` is the continuity clause of ThetaKernel restricted to admissible
 compact periods, with the distinguished-place prescription fixed.
 `h_ThetaKernel_nonzero` specifies the already chosen nonzero Schwartz input.
* `h_PolarizedPairing` is the strict-positivity clause of PolarizedPairing, specialized to the supplied
 conjugate pairing on complex surfaces. Purity and closedness are explicit.
 PolarizedPairing's proposed integral operator is undefined in its committed specification;
 the pairing therefore remains the same explicit interface as in PairingContinuity.
* GaussianConvergence is unnecessary once the ThetaKernel continuity output is supplied. ThetaKernel's
 factorization and level clauses are also unnecessary for this implication.

Pairing continuity is needed in addition to these prerequisite outputs; it is
already a natural hypothesis of the committed PairingContinuity target, not a new condition.
Instantiating the shared smooth topology, actual integration, and period-chart
identifications remains geometric interface work, as in the specifications.
-/

open scoped _root_.Manifold ContDiff _root_.Topology

abbrev SurfaceTwoForm (X : Type*) [TopologicalSpace X]
    [ChartedSpace (Fin 2 → ℂ) X] :=
  DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin 2 → ℂ) X 2

/-- The committed PairingContinuity implication, with every original hypothesis retained. -/
theorem persistence_of_nonzero_top_form_pairing
    {X Φ RationalSplitting : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace (Fin 2 → ℂ) X]
    [IsManifold 𝓘(ℂ, Fin 2 → ℂ) ∞ X]
    (smoothTopology : TopologicalSpace (SurfaceTwoForm X))
    (theta : Φ → RationalSplitting → SurfaceTwoForm X)
    (pairing : SurfaceTwoForm X → SurfaceTwoForm X → ℂ)
    (φ : Φ)
    (s₀ : RationalSplitting)
    (admissible : RationalSplitting → Prop)
    (s : ℕ → RationalSplitting)
    (h_admissible : ∀ n, admissible (s n))
    (h_converges :
      letI := smoothTopology
      Filter.Tendsto (fun n => theta φ (s n))
        Filter.atTop (𝓝 (theta φ s₀)))
    (h_pairing_continuous :
      letI := smoothTopology
      ContinuousAt (fun η => pairing (theta φ s₀) η)
        (theta φ s₀))
    (h_self : pairing (theta φ s₀) (theta φ s₀) ≠ 0) :
    ∃ s' : RationalSplitting,
      admissible s' ∧
      pairing (theta φ s₀) (theta φ s') ≠ 0 := by
  let _ := smoothTopology
  have h_limit := h_pairing_continuous.tendsto.comp h_converges
  obtain ⟨n, hn⟩ := (h_limit.eventually_ne h_self).exists
  exact ⟨s n, h_admissible n, hn⟩

/-- Approximation in parameter space and continuity suffice; only the
admissible parameter values need lie in the continuity domain. -/
theorem exists_pairing_ne_zero_of_approximation
    {P F S : Type*} [PseudoMetricSpace P] [TopologicalSpace F]
    (p₀ : P) (period : S → P) (admissible : S → Prop)
    (theta : P → F) (pairing : F → F → ℂ)
    (h_approx : ∀ ε : ℝ, 0 < ε →
      ∃ s, admissible s ∧ dist (period s) p₀ < ε)
    (h_theta : ContinuousWithinAt theta
      {p | ∃ s, admissible s ∧ period s = p} p₀)
    (h_pairing : ContinuousAt (pairing (theta p₀)) (theta p₀))
    (h_self : pairing (theta p₀) (theta p₀) ≠ 0) :
    ∃ s, admissible s ∧ pairing (theta p₀) (theta (period s)) ≠ 0 := by
  have h_ne := (h_pairing.tendsto.comp h_theta).eventually_ne h_self
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp h_ne
  obtain ⟨s, hs, hdist⟩ := h_approx ε hε
  exact ⟨s, hs, hball ⟨hdist, ⟨s, hs, rfl⟩⟩⟩

open OAI.Analysis.DifferentialForms.Coordinates.LocalApproximation _root_.Module
open scoped _root_.Matrix.Norms.Elementwise

/-- Exactly the orthogonality, nondegeneracy, orthocomplement, and new-sign
conditions in the conclusion of the committed LocalApproximation specification. -/
def NewSignsSplitting
    {E Place : Type*} [Field E] [Algebra ℚ E] [NumberField E]
    [NumberField.IsCMField E]
    (σ : Place → E →ₐ[ℚ] ℂ) (a : Fin 2 → E)
    (dNew : Fin 2 → Place → Bool) (η : Place → ℝ)
    (b : Basis (Fin 2) E (DifferentialForms.Coordinates.LocalApproximation.W E)) : Prop :=
  DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0 ∧
  (∀ i, DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i) ≠ 0) ∧
  (∀ y : DifferentialForms.Coordinates.LocalApproximation.W E, y ∈ Submodule.span E {b 1} ↔ DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) y = 0) ∧
  (∀ i τ, 0 < (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dNew i τ) : ℝ) *
    η τ * (σ τ (DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i))).re)

/-- Conditional manuscript application for the same chosen total Schwartz
input. LocalApproximation is assumed as a proposition, never invoked as a statement stub.
The old and new forms live on the same compact complex surface. -/
theorem persistence_from_prerequisites
    {E Place X Φ : Type*}
    [Field E] [Algebra ℚ E] [NumberField E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Fintype Place]
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] [ChartedSpace (Fin 2 → ℂ) X]
    [IsManifold 𝓘(ℂ, Fin 2 → ℂ) ∞ X]
    [IsManifold 𝓘(ℝ, Fin 2 → ℂ) ∞ X]
    (σ : Place → E →ₐ[ℚ] ℂ) (μ : Place)
    (a : Fin 2 → E) (dOld dNew : Fin 2 → Place → Bool)
    (η : Place → ℝ) (Qμ : X → Submodule ℂ DifferentialForms.Coordinates.LocalApproximation.MuAmbient)
    (smoothTopology : TopologicalSpace (SurfaceTwoForm X))
    (theta : Φ → DifferentialForms.Coordinates.LocalApproximation.PeriodData Place X μ → SurfaceTwoForm X)
    (pairing : SurfaceTwoForm X → SurfaceTwoForm X → ℂ)
    (φ : Φ)
    (h_LocalApproximation : ∀ ε : ℝ, 0 < ε →
      ∃ b : Basis (Fin 2) E (DifferentialForms.Coordinates.LocalApproximation.W E),
        DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0 ∧
        (∀ i, DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i) ≠ 0) ∧
        (∀ y : DifferentialForms.Coordinates.LocalApproximation.W E,
          y ∈ Submodule.span E {b 1} ↔ DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) y = 0) ∧
        (∀ i τ, 0 < (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dNew i τ) : ℝ) *
          η τ * (σ τ (DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i))).re) ∧
        (∀ τ : {τ : Place // τ ≠ μ},
          dist ((DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ b dNew).2 τ)
            ((DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ (Pi.basisFun E (Fin 2)) dOld).2 τ) < ε) ∧
        (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ b dNew).1 =
          (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ (Pi.basisFun E (Fin 2)) dOld).1)
    (h_ThetaKernel_continuous :
      let _ := smoothTopology
      ContinuousWithinAt (fun p => theta φ (Qμ, p))
        {p | ∃ b : Basis (Fin 2) E (DifferentialForms.Coordinates.LocalApproximation.W E),
          NewSignsSplitting σ a dNew η b ∧
          (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ b dNew).2 = p}
        (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ (Pi.basisFun E (Fin 2)) dOld).2)
    (h_ThetaKernel_nonzero :
      theta φ (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ (Pi.basisFun E (Fin 2)) dOld) ≠ 0)
    (h_type : DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Fin 2 → ℂ) X 2 0
      (theta φ (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ (Pi.basisFun E (Fin 2)) dOld)).val)
    (h_closed : DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d
      (theta φ (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ (Pi.basisFun E (Fin 2)) dOld)) = 0)
    (h_PolarizedPairing : ∀ form : SurfaceTwoForm X,
      DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Fin 2 → ℂ) X 2 0 form.val →
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 → form ≠ 0 →
      0 < (Complex.I ^ (2 * 2) * pairing form form).re)
    (h_pairing_continuous :
      let _ := smoothTopology
      let ξ := theta φ (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ (Pi.basisFun E (Fin 2)) dOld)
      ContinuousAt (pairing ξ) ξ) :
    ∃ b : Basis (Fin 2) E (DifferentialForms.Coordinates.LocalApproximation.W E),
      NewSignsSplitting σ a dNew η b ∧
      (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ b dNew).1 =
        (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ (Pi.basisFun E (Fin 2)) dOld).1 ∧
      pairing (theta φ (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ (Pi.basisFun E (Fin 2)) dOld))
        (theta φ (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ b dNew)) ≠ 0 := by
  classical
  let _ := smoothTopology
  let p₀ := (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ (Pi.basisFun E (Fin 2)) dOld).2
  let period := fun b : Basis (Fin 2) E (DifferentialForms.Coordinates.LocalApproximation.W E) => (DifferentialForms.Coordinates.LocalApproximation.totalPeriod σ μ Qμ b dNew).2
  let Θ := fun p => theta φ (Qμ, p)
  have h_approx : ∀ ε : ℝ, 0 < ε →
      ∃ b, NewSignsSplitting σ a dNew η b ∧ dist (period b) p₀ < ε := by
    intro ε hε
    obtain ⟨b, horth, hnondeg, hcompl, hsign, hdist, _⟩ := h_LocalApproximation ε hε
    exact ⟨b, ⟨horth, hnondeg, hcompl, hsign⟩, (dist_pi_lt_iff hε).mpr hdist⟩
  have h_self : pairing (Θ p₀) (Θ p₀) ≠ 0 := by
    intro hz
    have hpos := h_PolarizedPairing (Θ p₀) h_type h_closed h_ThetaKernel_nonzero
    simp only [hz, mul_zero, Complex.zero_re, lt_self_iff_false] at hpos
  obtain ⟨b, hb, hpair⟩ := exists_pairing_ne_zero_of_approximation
    p₀ period (NewSignsSplitting σ a dNew η) Θ pairing
    h_approx h_ThetaKernel_continuous h_pairing_continuous h_self
  exact ⟨b, hb, rfl, hpair⟩

end OAI.Analysis.HodgeTheory.PairingContinuity
