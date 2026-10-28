import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalProjector
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactComplex

/-! # Intertwining Basis -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntertwiningBasis.CM

noncomputable section

section

/-! ThetaCycle: local matrix formulas for the actual complex basis change and source projector. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open _root_.Module

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

theorem paired_basis_change_first (places : HeckeCycles.GeometricSource.CM.Places K) (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (x : ComplexTransition.CM.TotalAmbient K) (i : Fin 2) (τ : Fin places.count) (j : Fin 3) :
    (Symplectic.CM.galoisToPaired K places (ComplexTransition.CM.complexTensorBasisChange K b x i) τ).1 j =
      (Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) b *ᵥ
        (fun k => (Symplectic.CM.galoisToPaired K places (x k) τ).1 j)) i := by
  simp [Symplectic.CM.galoisToPaired_apply, ComplexTransition.CM.complexTensorBasisChange, Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix,
    HeckeCycles.ReferenceDatum.CM.embeddings, Matrix.mulVec, dotProduct]

theorem paired_basis_change_second (places : HeckeCycles.GeometricSource.CM.Places K) (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (x : ComplexTransition.CM.TotalAmbient K) (i : Fin 2) (τ : Fin places.count) (j : Fin 3) :
    (Symplectic.CM.galoisToPaired K places (ComplexTransition.CM.complexTensorBasisChange K b x i) τ).2 j =
      ((Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) b).map star *ᵥ
        (fun k => (Symplectic.CM.galoisToPaired K places (x k) τ).2 j)) i := by
  simp [Symplectic.CM.galoisToPaired_apply, ComplexTransition.CM.complexTensorBasisChange, Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix,
    HeckeCycles.ReferenceDatum.CM.embeddings, Matrix.mulVec, dotProduct]

theorem paired_source_projector (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Ambient K) (τ : Fin places.count) :
    Symplectic.CM.galoisToPaired K places (CompactComplex.CM.sourcePeriodProjector K B places d z w) τ =
      if τ = places.distinguished then
        CompactComplex.CM.distinguishedProjection K B z (Symplectic.CM.galoisToPaired K places w τ)
      else if d (places.representative τ) then (0, (Symplectic.CM.galoisToPaired K places w τ).2)
      else ((Symplectic.CM.galoisToPaired K places w τ).1, 0) := by
  change Symplectic.CM.galoisToPaired K places ((Symplectic.CM.galoisToPaired K places).symm
    (CompactComplex.CM.pairedLineProjector K B places d z (Symplectic.CM.galoisToPaired K places w))) τ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end

section

/-! ThetaCycle: the transported source projections are the actual compact-period matrices. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open _root_.Module

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

theorem compact_projector_intertwines_first (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Gal(K/ℚ) → Bool) (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (z : HeckeCycles.GeometricSource.CM.BallChart) (x : ComplexTransition.CM.TotalAmbient K) (τ : Fin places.count) (hτ : τ ≠ places.distinguished)
    (i : Fin 2) (j : Fin 3) :
    (Symplectic.CM.galoisToPaired K places
      (ComplexTransition.CM.complexTensorBasisChange K b (TotalProjector.CM.totalSourceProjector K B places d z x) i) τ).1 j =
    ((Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) b (fun k => d k (places.representative τ))).1 *ᵥ
      (fun k => (Symplectic.CM.galoisToPaired K places (ComplexTransition.CM.complexTensorBasisChange K b x k) τ).1 j)) i := by
  let v := fun k => (Symplectic.CM.galoisToPaired K places (x k) τ).1 j
  let ds := fun k => d k (places.representative τ)
  let M := Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) b
  have hm : (fun k => (Symplectic.CM.galoisToPaired K places (TotalProjector.CM.totalSourceProjector K B places d z x k) τ).1 j) =
      CompactComplex.CM.boolDiagonal (fun k => !ds k) *ᵥ v := by
    funext k
    change (Symplectic.CM.galoisToPaired K places (CompactComplex.CM.sourcePeriodProjector K B places (d k) z (x k)) τ).1 j = _
    rw [paired_source_projector]
    cases hd : d k (places.representative τ) <;>
      simp [hτ, hd, CompactComplex.CM.boolDiagonal, Matrix.mulVec_diagonal, ds, v]
  have hb : (fun k => (Symplectic.CM.galoisToPaired K places (ComplexTransition.CM.complexTensorBasisChange K b x k) τ).1 j) = M *ᵥ v := by
    funext k
    exact paired_basis_change_first K places b x k τ j
  rw [paired_basis_change_first, hm, hb, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (CompactComplex.CM.compact_period_selected_lines (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) b ds).1]

theorem compact_projector_intertwines_second (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Gal(K/ℚ) → Bool) (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (z : HeckeCycles.GeometricSource.CM.BallChart) (x : ComplexTransition.CM.TotalAmbient K) (τ : Fin places.count) (hτ : τ ≠ places.distinguished)
    (i : Fin 2) (j : Fin 3) :
    (Symplectic.CM.galoisToPaired K places
      (ComplexTransition.CM.complexTensorBasisChange K b (TotalProjector.CM.totalSourceProjector K B places d z x) i) τ).2 j =
    ((Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) b (fun k => d k (places.representative τ))).2 *ᵥ
      (fun k => (Symplectic.CM.galoisToPaired K places (ComplexTransition.CM.complexTensorBasisChange K b x k) τ).2 j)) i := by
  let v := fun k => (Symplectic.CM.galoisToPaired K places (x k) τ).2 j
  let ds := fun k => d k (places.representative τ)
  let M := (Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) b).map star
  have hm : (fun k => (Symplectic.CM.galoisToPaired K places (TotalProjector.CM.totalSourceProjector K B places d z x k) τ).2 j) =
      CompactComplex.CM.boolDiagonal ds *ᵥ v := by
    funext k
    change (Symplectic.CM.galoisToPaired K places (CompactComplex.CM.sourcePeriodProjector K B places (d k) z (x k)) τ).2 j = _
    rw [paired_source_projector]
    cases hd : d k (places.representative τ) <;>
      simp [hτ, hd, CompactComplex.CM.boolDiagonal, Matrix.mulVec_diagonal, ds, v]
  have hb : (fun k => (Symplectic.CM.galoisToPaired K places (ComplexTransition.CM.complexTensorBasisChange K b x k) τ).2 j) = M *ᵥ v := by
    funext k
    exact paired_basis_change_second K places b x k τ j
  rw [paired_basis_change_second, hm, hb, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (CompactComplex.CM.compact_period_selected_lines (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) b ds).2]

end

/-! ThetaCycle: the distinguished total period projector is unchanged by the
multiplicity basis change. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open _root_.Module

theorem linear_map_matrix_combination {I J : Type*} [Fintype I] [Fintype J]
    (f : (J → ℂ) →ₗ[ℂ] (J → ℂ)) (M : Matrix I I ℂ) (v : I → J → ℂ) (i : I) (j : J) :
    f (fun l => (M *ᵥ (fun k => v k l)) i) j = (M *ᵥ (fun k => f (v k) j)) i := by
  have h : (fun l => (M *ᵥ (fun k => v k l)) i) = ∑ k, M i k • v k := by
    funext l
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [h, map_sum]
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply]

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

theorem distinguished_projector_intertwines (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Gal(K/ℚ) → Bool) (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (z : HeckeCycles.GeometricSource.CM.BallChart) (x : ComplexTransition.CM.TotalAmbient K) (i : Fin 2) :
    Symplectic.CM.galoisToPaired K places
      (ComplexTransition.CM.complexTensorBasisChange K b (TotalProjector.CM.totalSourceProjector K B places d z x) i) places.distinguished =
    CompactComplex.CM.distinguishedProjection K B z
      (Symplectic.CM.galoisToPaired K places (ComplexTransition.CM.complexTensorBasisChange K b x i) places.distinguished) := by
  let τ := places.distinguished
  let M := Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) b
  have hp (k : Fin 2) : Symplectic.CM.galoisToPaired K places (TotalProjector.CM.totalSourceProjector K B places d z x k) τ =
      CompactComplex.CM.distinguishedProjection K B z (Symplectic.CM.galoisToPaired K places (x k) τ) := by
    change Symplectic.CM.galoisToPaired K places (CompactComplex.CM.sourcePeriodProjector K B places (d k) z (x k)) τ = _
    rw [paired_source_projector]
    simp only [τ, ite_true]
  apply Prod.ext
  · funext j
    change (Symplectic.CM.galoisToPaired K places
      (ComplexTransition.CM.complexTensorBasisChange K b (TotalProjector.CM.totalSourceProjector K B places d z x) i) τ).1 j =
        CompactComplex.CM.ballLineProjection z (Symplectic.CM.galoisToPaired K places (ComplexTransition.CM.complexTensorBasisChange K b x i) τ).1 j
    rw [paired_basis_change_first]
    simp only [hp]
    have hb : (Symplectic.CM.galoisToPaired K places (ComplexTransition.CM.complexTensorBasisChange K b x i) τ).1 =
        fun l => (M *ᵥ (fun k => (Symplectic.CM.galoisToPaired K places (x k) τ).1 l)) i := by
      funext l
      exact paired_basis_change_first K places b x i τ l
    rw [hb]
    exact (linear_map_matrix_combination (CompactComplex.CM.ballLineProjection z) M
      (fun k => (Symplectic.CM.galoisToPaired K places (x k) τ).1) i j).symm
  · funext j
    change (Symplectic.CM.galoisToPaired K places
      (ComplexTransition.CM.complexTensorBasisChange K b (TotalProjector.CM.totalSourceProjector K B places d z x) i) τ).2 j =
        CompactComplex.CM.ballAnnihilatorProjection (B.b : ℂ) z
          (Symplectic.CM.galoisToPaired K places (ComplexTransition.CM.complexTensorBasisChange K b x i) τ).2 j
    rw [paired_basis_change_second]
    simp only [hp]
    have hb : (Symplectic.CM.galoisToPaired K places (ComplexTransition.CM.complexTensorBasisChange K b x i) τ).2 =
        fun l => (M.map star *ᵥ (fun k => (Symplectic.CM.galoisToPaired K places (x k) τ).2 l)) i := by
      funext l
      exact paired_basis_change_second K places b x i τ l
    rw [hb]
    exact (linear_map_matrix_combination (CompactComplex.CM.ballAnnihilatorProjection (B.b : ℂ) z) (M.map star)
      (fun k => (Symplectic.CM.galoisToPaired K places (x k) τ).2) i j).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntertwiningBasis.CM
