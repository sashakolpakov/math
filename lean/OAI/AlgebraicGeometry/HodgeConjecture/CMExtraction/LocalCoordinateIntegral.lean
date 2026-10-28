import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalCoordinateEntries
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralBound

/-! # Local Coordinate Integral -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalCoordinateIntegral

noncomputable section

/-! The actual split coordinate matrix is integral at every sufficiently
large completely split prime, uniformly in the chosen local embeddings. -/

open scoped Classical _root_.Matrix

theorem localSymplecticChange_integral_above_bound
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {Place : Type*} [Fintype Place] [DecidableEq Place]
    (θ : E) (hθ : θ ≠ 0) (hθc : NumberField.IsCMField.complexConj E θ = -θ)
    (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Place × Fin 3) (Place × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) = RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm E θ H x y) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], N < q →
      ∀ [Algebra E ℚ_[q]] [IsScalarTower ℚ E ℚ_[q]]
        (σ : Place → E →ₐ[ℚ] ℚ_[q])
        (hσ : Function.Bijective (RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization.splitPairingEmbeddings E ℚ_[q] σ)) (i j),
        ‖(RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange E ℚ_[q] σ hσ θ hθ hθc H hH hHerm e he).val i j‖ ≤ 1 := by
  let coeff : (Bool × Fin 3) × (Sum (Place × Fin 3) (Place × Fin 3)) → E :=
    fun k => LocalCoordinateEntries.splitCoordinateCoefficient E θ H (e.symm (Pi.single k.2 1)) k.1.1 k.1.2
  obtain ⟨N, hN, hbound⟩ := PadicIntegralBound.Local.finite_coefficients_padic_integral_bound coeff
  refine ⟨N, hN, ?_⟩
  intro q hq hlarge hAlg hTower σ hσ i j
  cases i with
  | inl p =>
    have heq := LocalCoordinateEntries.localSymplecticChange_rational_entry E ℚ_[q] σ hσ θ hθ H hH e
      hθc hHerm he false p.1 p.2 j
    change (RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange E ℚ_[q] σ hσ θ hθ hθc H hH hHerm e he).val (.inl p) j =
      σ p.1 (coeff ((false, p.2), j)) at heq
    rw [heq]
    exact hbound q hlarge (σ p.1).toRingHom ((false, p.2), j)
  | inr p =>
    have heq := LocalCoordinateEntries.localSymplecticChange_rational_entry E ℚ_[q] σ hσ θ hθ H hH e
      hθc hHerm he true p.1 p.2 j
    change (RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange E ℚ_[q] σ hσ θ hθ hθc H hH hHerm e he).val (.inr p) j =
      σ p.1 (coeff ((true, p.2), j)) at heq
    rw [heq]
    exact hbound q hlarge (σ p.1).toRingHom ((true, p.2), j)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalCoordinateIntegral
