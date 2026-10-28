import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalPhase
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteCoordinates

/-! # Phase -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Phase

noncomputable section

/-! Exact split phase formulas for the retained native local matrix
on the original completed PEL vectors. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalPhase.TestTransport

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime) (v : Multiplicity.Odd.Sign E)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))

theorem nativeCompletedPhase_inl (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) (τ : Fin s) (i : Fin 3) :
    ((FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he).val *ᵥ
      (fun j => RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e Y j))) (Sum.inl (τ, i)) =
      Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (τ, false)) (Y i) := by
  let μ := D.pel.reference.distinguished
  let : Algebra E (Padic q) := (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false)).toAlgebra
  let : IsScalarTower ℚ E (Padic q) := IsScalarTower.of_algebraMap_eq
    (fun a => by change (a : Padic q) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false) (a : E); simp)
  exact LocalPhase.TestTransport.completed_localSymplecticChange_inl E (Padic q)
    (fun j => GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D.pel (j, false))
    (ScalarBounds.ParameterChoices.native_split_embeddings_bijective E D.pel hg hq μ)
    (D.pel.reference.imaginaryScalar * Multiplicity.nativeCoefficient E D.pel.reference v)
    (LocalCoordinates.nativeTraceCoefficient_ne_zero E D.pel.reference hg.reference_admissible v)
    (LocalCoordinates.nativeTraceCoefficient_conjugate E D.pel.reference hg.reference_admissible v)
    (Multiplicity.nativeMatrix E D.pel.reference) (Multiplicity.nativeMatrix_det_ne_zero E D.pel.reference hg.reference_admissible)
    (Multiplicity.nativeMatrix_hermitian E D.pel.reference hg.reference_admissible) e
    (fun x y => (he x y).trans (Multiplicity.native_tensor_trace E D.pel.reference v x y).symm)
    (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection_continuous q) Y τ i

theorem nativeCompletedPhase_inr (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) (τ : Fin s) (i : Fin 3) :
    ((FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he).val *ᵥ
      (fun j => RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e Y j))) (Sum.inr (τ, i)) =
      ((LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (τ, false)
          (D.pel.reference.imaginaryScalar * Multiplicity.nativeCoefficient E D.pel.reference v) •
        (Multiplicity.nativeMatrix E D.pel.reference).map (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (τ, false))) *ᵥ
        (fun j => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (τ, true)) (Y j))) i := by
  let μ := D.pel.reference.distinguished
  let : Algebra E (Padic q) := (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false)).toAlgebra
  let : IsScalarTower ℚ E (Padic q) := IsScalarTower.of_algebraMap_eq
    (fun a => by change (a : Padic q) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false) (a : E); simp)
  have ht := LocalPhase.TestTransport.completed_localSymplecticChange_inr E (Padic q)
    (fun j => GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D.pel (j, false))
    (ScalarBounds.ParameterChoices.native_split_embeddings_bijective E D.pel hg hq μ)
    (D.pel.reference.imaginaryScalar * Multiplicity.nativeCoefficient E D.pel.reference v)
    (LocalCoordinates.nativeTraceCoefficient_ne_zero E D.pel.reference hg.reference_admissible v)
    (LocalCoordinates.nativeTraceCoefficient_conjugate E D.pel.reference hg.reference_admissible v)
    (Multiplicity.nativeMatrix E D.pel.reference) (Multiplicity.nativeMatrix_det_ne_zero E D.pel.reference hg.reference_admissible)
    (Multiplicity.nativeMatrix_hermitian E D.pel.reference hg.reference_admissible) e
    (fun x y => (he x y).trans (Multiplicity.native_tensor_trace E D.pel.reference v x y).symm)
    (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection_continuous q) Y τ i
  have hc : RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization.conjugateSplitEmbedding E (Padic q) (GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D.pel (τ, false)) =
      GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D.pel (τ, true) := by
    ext x
    exact (RingHom.congr_fun (GaloisDiscrete.ParameterChoices.nativeFieldEmbedding_conjugate D.pel hq τ false) x).symm
  rw [hc] at ht
  exact ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Phase
