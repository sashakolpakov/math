import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarBounds
import OAI.RepresentationTheory.Hecke.RadialDilation.ConcreteFinite
import OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Data
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalUnitaryPhase
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate

/-! # Auxiliary Finite Family -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryFiniteFamily

noncomputable section

/-! One native symplectic basis and finite coordinate lift support all
nonzero auxiliary test functions. Each test retains its actual scalar
power and exact native splitting formula. -/

open OAI.RepresentationTheory.Theta.Geometric.Data
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarBounds.ParameterChoices
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity
open scoped Classical _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)

theorem native_finite_auxiliary_radial_family
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (v : Multiplicity.Odd.Sign E) :
    ∃ (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
      (_he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
        Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
      (u : MpF), FiniteDilation.NativeFiniteCoordinateIdentity E D e u ∧
      ∀ φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 →
      ∃ (r : Eˣ) (M : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) ℚ)
        (Uq : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (ξ : ℂ),
        0 < M ∧ (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
        γ.val = RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix E e (r : E) ∧
        (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
          (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
            if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
        Function.Injective (AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ) ∧
        RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ξ ∧
        (∀ (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q), (Uq b).val x =
          (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
            b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i)) ∧
        (∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
          D.weil.finiteAction γ (AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b) =
            ξ • AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ (Uq b)) := by
  let μ := D.pel.reference.distinguished
  let : Algebra E ℚ_[q] := (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false)).toAlgebra
  let : IsScalarTower ℚ E ℚ_[q] := IsScalarTower.of_algebraMap_eq
    (fun a => by change (a : ℚ_[q]) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false) (a : E); simp)
  let P := D.pel.reference
  have hP := hg.reference_admissible
  obtain ⟨e, he⟩ := Multiplicity.native_symplectic_coordinates E P hP v
  have he' : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm E (P.imaginaryScalar * Multiplicity.nativeCoefficient E P v) (Multiplicity.nativeMatrix E P) x y :=
    fun x y => (he x y).trans (Multiplicity.native_tensor_trace E P v x y).symm
  obtain ⟨r, M, hM, hr, hval, _, hcompact, hactive, _, haway⟩ :=
    ScalarBounds.ParameterChoices.exists_native_scalar_with_bounds E D.pel hg hq ιE μ
  have hδ : NumberField.IsCMField.complexConj E P.imaginaryScalar = -P.imaginaryScalar :=
    hP.2.2.2.2.2.2.2.1
  have ha := Multiplicity.nativeCoefficient_real E P hP v
  have hθ : P.imaginaryScalar * Multiplicity.nativeCoefficient E P v ≠ 0 := by
    rw [Multiplicity.native_orientedCoefficient E P hP v]
    exact neg_ne_zero.mpr (Multiplicity.Odd.imaginaryCoefficient_ne_zero E v)
  have hθc : NumberField.IsCMField.complexConj E
      (P.imaginaryScalar * Multiplicity.nativeCoefficient E P v) = -(P.imaginaryScalar * Multiplicity.nativeCoefficient E P v) := by
    rw [Multiplicity.native_orientedCoefficient E P hP v]
    change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (-Multiplicity.Odd.imaginaryCoefficient E v) = - -Multiplicity.Odd.imaginaryCoefficient E v
    rw [map_neg, Multiplicity.Odd.imaginaryCoefficient_conjugate]
  let γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) ℚ := ⟨RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix E e (r : E),
    RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization.rationalScalarMatrix_symplectic E P.embeddings hP.1 P.imaginaryScalar
      (Multiplicity.nativeCoefficient E P v) hδ ha (Multiplicity.nativeMatrix E P) (Multiplicity.nativeMatrix_hermitian E P hP)
      e he' r hr⟩
  let σq := fun i => GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D.pel (i, false)
  have hσq := ScalarBounds.ParameterChoices.native_split_embeddings_bijective E D.pel hg hq μ
  let S := RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange E ℚ_[q] σq hσq
    (P.imaginaryScalar * Multiplicity.nativeCoefficient E P v) hθ hθc (Multiplicity.nativeMatrix E P)
    (Multiplicity.nativeMatrix_det_ne_zero E P hP) (Multiplicity.nativeMatrix_hermitian E P hP) e he'
  have hscalar : ∀ x, S.val *ᵥ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      RepresentationTheory.Hecke.RadialDilation.ScalarPhase.Realization.pairedScalarPhase q (RepresentationTheory.Hecke.RadialDilation.GeometricSplitScalar.Realization.splitScalarUnits σq r) (S.val *ᵥ x) :=
    RepresentationTheory.Hecke.RadialDilation.GeometricSplitScalar.Realization.geometric_split_scalar_identity E q σq hσq _ hθ hθc (Multiplicity.nativeMatrix E P)
      (Multiplicity.nativeMatrix_det_ne_zero E P hP) (Multiplicity.nativeMatrix_hermitian E P hP) e he' r hr γ rfl
  have hbounded : ∀ (p : ℕ) [Fact p.Prime], p ≠ q → ∃ B : ℝ,
      ∀ (N : ℕ) i j, ‖((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) γ) ^ N).val i j‖ ≤ B := by
    intro p hp hpq
    exact haway e p hpq
  obtain ⟨u, hu⟩ := RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.exists_finite_coordinate_lift q D.weil S
  refine ⟨e, he, u, ?_, ?_⟩
  · refine ⟨S, hu, ?_⟩
    intro g x
    rw [RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange_mulVec, RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange_mulVec]
    exact LocalUnitaryPhase.Intrinsic.rationalToSplitCoordinates_unitary E P ℚ_[q] σq hσq _ hθ
      (Multiplicity.nativeMatrix_det_ne_zero E P hP) e g x
  · intro φ hφ
    obtain ⟨N, ξ, hN, hNM, hξ, hf⟩ := AuxiliaryRadialPower.Local.actual_rational_auxiliary_radial_power q μ hLocalWeil D.weil φ S γ
      (RepresentationTheory.Hecke.RadialDilation.GeometricSplitScalar.Realization.splitScalarUnits σq r) u hu hscalar hcompact hbounded M hM
      (by rw [Units.val_inv_eq_inv_val]; exact hactive)
    let Uq := RepresentationTheory.Hecke.RadialDilation.Mem.Realization.normalizedScalarSubstitution q (((RepresentationTheory.Hecke.RadialDilation.GeometricSplitScalar.Realization.splitScalarUnits σq r μ)⁻¹) ^ N : ℚ_[q]ˣ).val (N * M)
      (RepresentationTheory.Hecke.RadialDilation.ScalarPowerFactorization.Realization.padic_scalar_norm_power q (RepresentationTheory.Hecke.RadialDilation.GeometricSplitScalar.Realization.splitScalarUnits σq r μ)⁻¹ M N
        (by rw [Units.val_inv_eq_inv_val]; exact hactive))
    have hvN : ∀ i : Fin s × Bool, (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel i (r ^ N : Eˣ)).valuation =
        if i = (μ, true) then ((N * M : ℕ) : ℤ)
        else if i = (μ, false) then -((N * M : ℕ) : ℤ) else 0 := by
      intro i
      rw [Units.val_pow_eq_pow_val, map_pow, Padic.valuation_pow, hval]
      split_ifs <;> simp only [Nat.cast_mul, mul_neg, mul_zero]
    refine ⟨r ^ N, N * M, γ ^ N, Uq, ξ, hNM, RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.cm_norm_one_power E r hr N, ?_,
      ScalarBounds.ParameterChoices.native_global_splitting_of_local E D.pel hg hq ιE μ (r ^ N) (N * M)
        (by intro i; have hi := hvN i; split_ifs at hi ⊢ <;> exact hi),
      AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding_injective q μ D.weil u φ hφ,
      ⟨8, by decide, hξ⟩, ?_, hf⟩
    · change RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix E e (r : E) ^ N = RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix E e (r ^ N : Eˣ).val
      rw [RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix_pow, Units.val_pow_eq_pow_val]
    · intro b x
      exact RepresentationTheory.Hecke.RadialDilation.Mem.Realization.normalizedScalarSubstitution_apply q _ (N * M) _ b x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryFiniteFamily
