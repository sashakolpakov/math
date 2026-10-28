import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation

/-! # Finite Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteCoordinates

noncomputable section

/-! Choose an actual finite coordinate lift for a previously fixed
rational basis, retaining its exact integral local matrix. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

def nativeCoordinateBound
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (v : Multiplicity.Odd.Sign E)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y)) : ℕ :=
  (LocalCoordinates.nativeLocalCoordinateMatrix_integral_bound E P hP v e he).choose

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime) (v : Multiplicity.Odd.Sign E)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))

def nativeFiniteCoordinateMatrix : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) ℚ_[q] := by
  let μ := D.pel.reference.distinguished
  let : Algebra E ℚ_[q] := (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false)).toAlgebra
  let : IsScalarTower ℚ E ℚ_[q] := IsScalarTower.of_algebraMap_eq
    (fun a => by change (a : ℚ_[q]) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false) (a : E); simp)
  exact LocalCoordinates.nativeLocalCoordinateMatrix E D.pel.reference hg.reference_admissible v e he ℚ_[q]
    (fun i => GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D.pel (i, false))
    (ScalarBounds.ParameterChoices.native_split_embeddings_bijective E D.pel hg hq μ)

theorem nativeFiniteCoordinateMatrix_integral
    (hlarge : nativeCoordinateBound E D.pel.reference hg.reference_admissible v e he < q) :
    ∀ i j, ‖(nativeFiniteCoordinateMatrix E D hg hq v e he).val i j‖ ≤ 1 := by
  let μ := D.pel.reference.distinguished
  let : Algebra E ℚ_[q] := (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false)).toAlgebra
  let : IsScalarTower ℚ E ℚ_[q] := IsScalarTower.of_algebraMap_eq
    (fun a => by change (a : ℚ_[q]) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false) (a : E); simp)
  exact (LocalCoordinates.nativeLocalCoordinateMatrix_integral_bound E D.pel.reference hg.reference_admissible v e he).choose_spec.2
    q hlarge (fun i => GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D.pel (i, false))
      (ScalarBounds.ParameterChoices.native_split_embeddings_bijective E D.pel hg hq μ)

theorem nativeFiniteCoordinateMatrix_unitary (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.pel.reference.b)
    (x : Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ_[q]) :
    (nativeFiniteCoordinateMatrix E D hg hq v e he).val *ᵥ
      ((RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix E D.pel.reference e g).map (algebraMap ℚ ℚ_[q]) *ᵥ x) =
      LocalUnitaryPhase.Intrinsic.localUnitaryPhase E D.pel.reference ℚ_[q]
        (fun i => GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D.pel (i, false)) g
        ((nativeFiniteCoordinateMatrix E D hg hq v e he).val *ᵥ x) := by
  let μ := D.pel.reference.distinguished
  let : Algebra E ℚ_[q] := (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false)).toAlgebra
  let : IsScalarTower ℚ E ℚ_[q] := IsScalarTower.of_algebraMap_eq
    (fun a => by change (a : ℚ_[q]) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (μ, false) (a : E); simp)
  unfold nativeFiniteCoordinateMatrix
  exact LocalCoordinates.nativeLocalCoordinateMatrix_unitary E D.pel.reference hg.reference_admissible v e he
    ℚ_[q] _ _ g x

theorem exists_native_fixed_finite_coordinates :
    ∃ u : MpF,
      D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
        (nativeFiniteCoordinateMatrix E D hg hq v e he) ∧
      FiniteDilation.NativeFiniteCoordinateIdentity E D e u := by
  obtain ⟨u, hu⟩ := RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.exists_finite_coordinate_lift q D.weil (nativeFiniteCoordinateMatrix E D hg hq v e he)
  exact ⟨u, hu, nativeFiniteCoordinateMatrix E D hg hq v e he, hu,
    nativeFiniteCoordinateMatrix_unitary E D hg hq v e he⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteCoordinates
