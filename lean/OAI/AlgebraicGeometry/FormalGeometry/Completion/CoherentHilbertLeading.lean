import OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentTwistInjections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialComparison

/-! # Coherent Hilbert Leading -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentHilbertLeading

noncomputable section

/-! Tensoring a coherent module by any line bundle preserves its Hilbert
degree and leading coefficient when global functions form an infinite field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ} {X : Scheme.{u}}
  [IsLocallyNoetherian X] [CompactSpace X] [Infinite Γ(X, ⊤)]
  (hfield : IsField Γ(X, ⊤))
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

include hfield

theorem coherentLineBundle_hilbert_degree_leadingCoeff_of_nonzero
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (hM : ¬ IsZero M)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) j).natDegree =
      (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M j).natDegree ∧
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) j).leadingCoeff =
      (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M j).leadingCoeff := by
  obtain ⟨n, hn⟩ := CoherentTwistInjections.Construction.closedProjectiveModuleLineBundle_eventually_injections hfield f M L j
  obtain ⟨a, c, ha, hc⟩ := hn n le_rfl
  have := ha
  have := hc
  obtain ⟨b₁, hb₁⟩ := ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_eventually_le_of_mono f a j
  obtain ⟨b₂, hb₂⟩ := ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_eventually_le_of_mono f c j
  have hN : ¬ IsZero (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) :=
    fun h => hM ((CoherentLineBundleTensor.Construction.coherentLineBundleTensor_isZero_iff M L).mp h)
  apply PolynomialComparison.Construction.polynomial_degree_leadingCoeff_eq_of_mutual_shift_bounds _ _
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_leadingCoeff_pos f _ j hN)
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_leadingCoeff_pos f M j hM) (max b₁ b₂) n
  · intro m hm
    simpa only [ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_twist, Polynomial.taylor_eval] using
      hb₂ m ((le_max_right _ _).trans hm)
  · intro m hm
    simpa only [ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_twist, Polynomial.taylor_eval] using
      hb₁ m ((le_max_left _ _).trans hm)

theorem coherentLineBundle_hilbert_degree_leadingCoeff
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) j).natDegree =
      (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M j).natDegree ∧
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) j).leadingCoeff =
      (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M j).leadingCoeff := by
  by_cases hM : IsZero M
  · have hN := (CoherentLineBundleTensor.Construction.coherentLineBundleTensor_isZero_iff M L).mpr hM
    have hp := HilbertPositivity.Construction.projectiveHilbertPolynomial_eq_zero_of_isZero (ClosedHilbertNumerics.Construction.coherentClosedDirectImage f M) j
      ((Scheme.Modules.pushforward f).map_isZero hM)
    have hq := HilbertPositivity.Construction.projectiveHilbertPolynomial_eq_zero_of_isZero
      (ClosedHilbertNumerics.Construction.coherentClosedDirectImage f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L)) j
      ((Scheme.Modules.pushforward f).map_isZero hN)
    change (Projective.Numerics.Construction.projectiveHilbertPolynomial _ _).natDegree = (Projective.Numerics.Construction.projectiveHilbertPolynomial _ _).natDegree ∧
      (Projective.Numerics.Construction.projectiveHilbertPolynomial _ _).leadingCoeff = (Projective.Numerics.Construction.projectiveHilbertPolynomial _ _).leadingCoeff
    rw [hp, hq]
    exact ⟨rfl, rfl⟩
  · exact coherentLineBundle_hilbert_degree_leadingCoeff_of_nonzero hfield f M hM L j

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentHilbertLeading
