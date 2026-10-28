import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedCoordinateChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.CoordinateRelations

/-! # Relation Invariance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.RelationInvariance

noncomputable section

/-! Having the degree relations of an actual saturated flat
Hilbert ideal is invariant under invertible coordinate changes,
unit row rescalings, and relabeling. -/
universe u v w
variable {R : Type u} [CommRing R] {n : ℕ} {ι : Type v}

def ConfigurationHasHilbertRelations (v : ι → Fin (n + 1) → R) (D : ℕ) (P : Polynomial ℚ) : Prop :=
  ∃ I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P,
    (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation v D).ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.ideal.toIdeal D

theorem configurationHasHilbertRelations_matrix_iff [Fintype ι] [DecidableEq ι]
    (v : ι → Fin (n + 1) → R) (D : ℕ) (P : Polynomial ℚ) :
    ConfigurationHasHilbertRelations v D P ↔
      ∃ I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P,
        (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix v D)).ker = HilbertScheme.Presentations.DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I.ideal D := by
  unfold ConfigurationHasHilbertRelations
  apply exists_congr
  intro I
  rw [CoordinateRelations.configurationMonomialMatrix_kernel]
  change _ ↔ Submodule.map (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n D).equivFun.toLinearMap _ =
    Submodule.map (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n D).equivFun.toLinearMap _
  exact (Submodule.map_injective_of_injective (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n D).equivFun.injective).eq_iff.symm

theorem configurationHasHilbertRelations_relabel_iff {κ : Type w}
    (v : ι → Fin (n + 1) → R) (e : κ ≃ ι) (D : ℕ) (P : Polynomial ℚ) :
    ConfigurationHasHilbertRelations (fun c => v (e c)) D P ↔ ConfigurationHasHilbertRelations v D P := by
  unfold ConfigurationHasHilbertRelations
  simp only [EvaluationInvariance.homogeneousConfigurationEvaluation_kernel_relabel]

variable [IsNoetherianRing R]

theorem configurationHasHilbertRelations_of_frameOrbit
    (v w : ι → Fin (n + 1) → R)
    (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) (s : ι → Rˣ)
    (h : ∀ z, w z = (s z : R) • T (v z)) (D : ℕ) (P : Polynomial ℚ)
    (H : ConfigurationHasHilbertRelations v D P) : ConfigurationHasHilbertRelations w D P := by
  obtain ⟨I, hI⟩ := H
  refine ⟨I.coordinateChange (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T), ?_⟩
  have hw : w = fun z j => (s z : R) * T (v z) j :=
    funext (fun z => funext (fun j => congrFun (h z) j))
  rw [hw]
  exact I.coordinateChange_configuration_kernel v D T s hI

theorem configurationHasHilbertRelations_frameOrbit_iff
    (v w : ι → Fin (n + 1) → R)
    (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) (s : ι → Rˣ)
    (h : ∀ z, w z = (s z : R) • T (v z)) (D : ℕ) (P : Polynomial ℚ) :
    ConfigurationHasHilbertRelations w D P ↔ ConfigurationHasHilbertRelations v D P := by
  refine ⟨?_, configurationHasHilbertRelations_of_frameOrbit v w T s h D P⟩
  apply configurationHasHilbertRelations_of_frameOrbit w v T.symm (fun z => (s z)⁻¹) ?_ D P
  intro z
  rw [h z, T.symm.map_smul, T.symm_apply_apply]
  change v z = (s z)⁻¹ • ((s z) • v z)
  rw [inv_smul_smul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.RelationInvariance
