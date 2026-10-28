import OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField
import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanNormCoordinates

/-! # Real Quadratic Field -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealQuadraticField

noncomputable section

/-! A real nonsplit quadratic algebra as an actual normed field. The norm
comes from a complex algebra embedding and preserves the native field operations. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField

variable (d : ℝ) (hns : ¬ IsSquare d)

def complexEmbedding : QuadraticLocalField.FieldModel ℝ d hns →ₐ[ℝ] ℂ := IsAlgClosed.lift

def complexEquiv : QuadraticLocalField.FieldModel ℝ d hns ≃ₐ[ℝ] ℂ :=
  AlgEquiv.ofBijective (complexEmbedding d hns) ⟨(complexEmbedding d hns).injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (complexEmbedding d hns).toLinearMap)
      ((QuadraticLocalField.model_finrank ℝ d hns).trans Complex.finrank_real_complex.symm)).mp
      (complexEmbedding d hns).injective⟩

instance realModelNormedField : NormedField (QuadraticLocalField.FieldModel ℝ d hns) :=
  NormedField.induced (QuadraticLocalField.FieldModel ℝ d hns) ℂ (complexEmbedding d hns) (complexEmbedding d hns).injective

instance realModelNormedAlgebra : NormedAlgebra ℝ (QuadraticLocalField.FieldModel ℝ d hns) where
  norm_smul_le r x := by
    change ‖complexEmbedding d hns (r • x)‖ ≤ ‖r‖ * ‖complexEmbedding d hns x‖
    rw [map_smul, norm_smul]

instance realModelComplete : CompleteSpace (QuadraticLocalField.FieldModel ℝ d hns) :=
  FiniteDimensional.complete ℝ (QuadraticLocalField.FieldModel ℝ d hns)

instance realModelLocallyCompact : LocallyCompactSpace (QuadraticLocalField.FieldModel ℝ d hns) :=
  (complexEquiv d hns).toLinearEquiv.toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.locallyCompactSpace

instance realModelMeasurable : MeasurableSpace (QuadraticLocalField.FieldModel ℝ d hns) := borel _
instance realModelBorel : BorelSpace (QuadraticLocalField.FieldModel ℝ d hns) := ⟨rfl⟩

theorem realModel_nondiscrete : ¬ DiscreteTopology (QuadraticLocalField.FieldModel ℝ d hns) := by
  intro h
  let : DiscreteTopology (QuadraticLocalField.FieldModel ℝ d hns) := h
  let e := (complexEquiv d hns).toLinearEquiv.toContinuousLinearEquiv.toHomeomorph
  have ho : IsOpen ({0} : Set ℂ) := by
    have he : e '' ({0} : Set (QuadraticLocalField.FieldModel ℝ d hns)) = ({0} : Set ℂ) := by
      rw [Set.image_singleton]
      congr 1
      exact map_zero (complexEquiv d hns)
    rw [← he]
    exact e.isOpenMap _ (isOpen_discrete _)
  exact not_isOpen_singleton (0 : ℂ) ho

theorem realModel_norm (x : QuadraticLocalField.FieldModel ℝ d hns) :
    Algebra.norm ℝ x = Complex.normSq (complexEquiv d hns x) := by
  rw [← Algebra.norm_eq_of_algEquiv (complexEquiv d hns), Algebra.norm_complex_eq]
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.RealQuadraticField
