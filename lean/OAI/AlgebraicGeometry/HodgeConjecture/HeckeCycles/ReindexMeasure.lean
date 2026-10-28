import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.TestReindex
import OAI.RepresentationTheory.Theta.AdelicTopology

/-! # Reindex Measure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReindexMeasure.CM

noncomputable section

/-! Exact transport of finite and adelic measures under coordinate relabeling. -/

open scoped Classical
open _root_.MeasureTheory OAI.RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction
variable {I J K : Type*}

def coordinates [MeasurableSpace K] (e : I ≃ J) : (I → K) ≃ᵐ (J → K) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; exact congrArg x (e.symm_apply_apply i)
  right_inv y := by funext j; exact congrArg y (e.apply_symm_apply j)
  measurable_toFun := Measurable.of_eval (fun j => measurable_pi_apply (e.symm j))
  measurable_invFun := Measurable.of_eval (fun i => measurable_pi_apply (e i))

theorem integral_map [MeasurableSpace K] [TopologicalSpace K]
    (e : I ≃ J) (μ : Measure (J → K)) (f : (I → K) → ℂ) :
    (∫ x, f x ∂μ.map (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm)) = ∫ y, f (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y) ∂μ :=
  (coordinates e.symm).measurableEmbedding.integral_map f

variable [Fintype I] [Fintype J]

def finiteMeasure (e : I ≃ J) (μ : Measure (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : Measure (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  μ.map (Finite.ReindexHeisenberg.CM.Pairing.coordinateEquiv e.symm)

instance finiteMeasure_haar (e : I ≃ J) (μ : Measure (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) [μ.IsAddHaarMeasure] :
    (finiteMeasure e μ).IsAddHaarMeasure := by
  unfold finiteMeasure
  infer_instance

omit [Fintype I] [Fintype J] in
theorem finite_integral (e : I ≃ J) (μ : Measure (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (f : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) :
    (∫ x, f x ∂ finiteMeasure e μ) = ∫ y, f (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y) ∂μ :=
  CM.integral_map e μ f

theorem adelic_map (e : I ≃ J) (μ : Measure (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) [SFinite μ] :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (finiteMeasure e μ) = (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ).map (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm) := by
  have hf : MeasurePreserving (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm (K := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) μ (finiteMeasure e μ) :=
    ⟨(coordinates e.symm).measurable, rfl⟩
  have hp := ((Real.TestReindex.CM.measurePreserving e.symm).prod hf).map_eq
  change Measure.map (RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv (ι := I)) _ =
    Measure.map (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm) (Measure.map (RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv (ι := J)) _)
  rw [← hp, Measure.map_map RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv.measurable
    ((Real.TestReindex.CM.measurePreserving e.symm).prod hf).measurable,
    Measure.map_map (show Measurable (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm (K := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) from
      (coordinates e.symm).measurable) RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv.measurable]
  rfl

theorem adelic_integral (e : I ≃ J) (μ : Measure (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) [SFinite μ]
    (f : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) :
    (∫ x, f x ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (finiteMeasure e μ)) =
      ∫ y, f (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y) ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ := by
  rw [adelic_map]
  exact CM.integral_map e (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ) f

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReindexMeasure.CM
