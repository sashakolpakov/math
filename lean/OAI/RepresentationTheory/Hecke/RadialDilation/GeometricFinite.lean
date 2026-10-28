import OAI.RepresentationTheory.Hecke.RadialDilation.SplitPrimeSupport
import OAI.RepresentationTheory.Hecke.RadialDilation.ConcreteFinite
import OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates
import OAI.RepresentationTheory.Hecke.RadialDilation.PairingTransport

/-! # Geometric Finite -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.GeometricFinite.Realization

noncomputable section

/-! The geometric CM construction supplies RadialDilation's finite input hypotheses without matrix bounds or eigenrelation assumptions. -/

open scoped Classical _root_.Matrix

variable {Place : Type*} [Fintype Place] [DecidableEq Place]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem geometric_finite_inputs_for_coordinates
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (hNormOneApproximation : Prerequisites.Core.NormOneApproximation.Proposition.{0})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (q : ℕ) [Fact q.Prime] [Algebra E ℚ_[q]] [IsScalarTower ℚ E ℚ_[q]]
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (σq : Place → E →ₐ[ℚ] ℚ_[q]) (hσq : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E ℚ_[q] σq))
    (δ t : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ht : NumberField.IsCMField.complexConj E t = t) (hδt : δ * t ≠ 0)
    (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Place × Fin 3) (Place × Fin 3) → ℚ))
    (he : ∀ x y, FramePositivity.Realization.coordinatePairing (e x) (e y) = SymplecticBasis.Realization.rationalTraceForm E (δ * t) H x y)
    (μ : Place) (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) :
    ∃ (r : Eˣ) (M : ℕ) (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (s : MpF)
      (Uq : Cm.radialInput q →ₗ[ℂ] Cm.radialInput q) (ξ : ℂ),
      0 < M ∧ (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
      γ.val = RationalCoordinates.Realization.rationalScalarMatrix E e (r : E) ∧
      Function.Injective (ConcreteFinite.Realization.coordinateRadialEmbedding q μ D s) ∧ Cm.finitePhase ξ ∧
      (∀ (b : Cm.radialInput q) (x : Mem.Realization.Position q), (Uq b).val x =
        (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
          b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i)) ∧
      (∀ b : Cm.radialInput q,
        D.finiteAction γ (ConcreteFinite.Realization.coordinateRadialEmbedding q μ D s b) =
          ξ • ConcreteFinite.Realization.coordinateRadialEmbedding q μ D s (Uq b)) := by
  obtain ⟨r, M, hM, hr, hcompact, hactive, haway⟩ := SplitPrimeSupport.Realization.exists_split_scalar_arithmetic hNormOneApproximation E q μ σq hσq
  let γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ := ⟨RationalCoordinates.Realization.rationalScalarMatrix E e (r : E),
    PairingTransport.Realization.rationalScalarMatrix_symplectic E σ hσ δ t hδ ht H hHerm e he r hr⟩
  have hθc : NumberField.IsCMField.complexConj E (δ * t) = -(δ * t) := by
    rw [map_mul, hδ, ht, neg_mul]
  let S := SplitScalarSymplectic.Realization.localSymplecticChange E ℚ_[q] σq hσq (δ * t) hδt hθc H hH hHerm e he
  have hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q (GeometricSplitScalar.Realization.splitScalarUnits σq r) (S.val *ᵥ x) :=
    GeometricSplitScalar.Realization.geometric_split_scalar_identity E q σq hσq (δ * t) hδt hθc H hH hHerm e he r hr γ rfl
  have hbounded : ∀ (p : ℕ) [Fact p.Prime], p ≠ q → ∃ R : ℝ,
      ∀ (N : ℕ) i j, ‖((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) γ) ^ N).val i j‖ ≤ R := by
    intro p hp hpq
    obtain ⟨R, hR⟩ := haway e p hpq
    exact ⟨R, hR⟩
  obtain ⟨N, s, Uq, ξ, _, hNM, _, hj, hξ, hUq, hfinite⟩ := ConcreteFinite.Realization.actual_finite_radial_inputs q μ hLocalWeil D
    S γ (GeometricSplitScalar.Realization.splitScalarUnits σq r) hscalar hcompact hbounded M hM hactive
  refine ⟨r ^ N, N * M, γ ^ N, s, Uq, ξ, hNM, RationalCoordinates.Realization.cm_norm_one_power E r hr N,
    ?_, hj, hξ, hUq, hfinite⟩
  change RationalCoordinates.Realization.rationalScalarMatrix E e (r : E) ^ N = RationalCoordinates.Realization.rationalScalarMatrix E e (r ^ N : Eˣ).val
  rw [RationalCoordinates.Realization.rationalScalarMatrix_pow, Units.val_pow_eq_pow_val]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.GeometricFinite.Realization
