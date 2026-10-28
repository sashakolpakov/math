import OAI.AlgebraicGeometry.HodgeConjecture.GeometricOperations
import OAI.Algebra.FieldTheory.ScalarDescentTrace
import OAI.AlgebraicGeometry.HodgeConjecture.FourProduct

/-! # Geometric Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.GeometricNormalization.Lefschetz.Geometry

noncomputable section

/-!
# LefschetzNormalization on actual geometric cycle-class images

The historical abstract theorem is instantiated with the constructed
twofold/fourfold products, canonical embedding tensors and geometric cycle
images. All four interface laws have proofs. Scalar descent is discharged
by the unconditional ScalarDescent proof. This intermediate theorem still names the
full DegreeTwo conclusions and the native ExteriorCohomology/LineBundleCycles/ThomClass result inputs; the separate
composition module discharges the available native inputs.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct Classical

def Conclusions : Prop := LefschetzNormalization.WeightOneInput ∧ LefschetzNormalization.AlbaneseInput ∧ LefschetzNormalization.DegreeTwoInput

theorem scalarTraceInput_proved : LefschetzNormalization.ScalarTraceInput :=
  Algebra.FieldTheory.ScalarDescentTrace.Core.scalar_trace_descent

theorem weightOne_fullness (h : LefschetzNormalization.WeightOneInput) : ComplexMultiplication.KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic := by
  intro A B f hhol hanti
  obtain ⟨n, hn, g, hg, he⟩ := h A B f hhol hanti
  refine ⟨(n : ℚ)⁻¹, g, hg, ?_⟩
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [he, smul_smul, inv_mul_cancel₀ hnQ, one_smul]

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

/-- The concrete tensor comparison never kills an embedding tensor in an
actual fourfold product. This uses the proved geometric Künneth map. -/
theorem fourClass_ne_zero {v : LefschetzNormalization.FourTypes E}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (hprod : IsLimit (Fan.mk X.toOver π)) (a : Fin 4 → LefschetzNormalization.G E) :
    GeometricFour.LefschetzNormalization.Geometry.fourClass E R X π a ≠ 0 := by
  apply FourProduct.CM.SurfaceConstruction.fourProduct_cup_ne_zero (fun i => (R i).abelianVariety.variety) X π hprod
    (fun i => (R i).complexComparison (LefschetzNormalization.embeddingGenerator E (a i)))
  intro i hzero
  exact ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector_ne_zero E _
    ((R i).complexComparison.injective (hzero.trans (map_zero _).symm))

/-- The comparison carries exactly the prescribed tensor line to the
span of the actual nonzero fourfold cohomology class. -/
theorem fourTensorLine_image {v : LefschetzNormalization.FourTypes E}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) (a : Fin 4 → LefschetzNormalization.G E) :
    (Submodule.span ℂ ({GeometricFour.LefschetzNormalization.Geometry.embeddingTensor E a} : Set (GeometricFour.LefschetzNormalization.Geometry.FourTensor E))).map
        (GeometricFour.LefschetzNormalization.Geometry.fourTensorComparison E R X π) =
      Submodule.span ℂ ({GeometricFour.LefschetzNormalization.Geometry.fourClass E R X π a} : Set (X.complexCohomology 4)) := by
  rw [Submodule.map_span, Set.image_singleton, GeometricFour.LefschetzNormalization.Geometry.fourTensorComparison_embedding]

theorem A₄_iff_tensorLine_algebraic (R : GeometricFour.LefschetzNormalization.Geometry.RealizationFamily E)
    (v : LefschetzNormalization.FourTypes E) (a : Fin 4 → LefschetzNormalization.G E) :
    GeometricFour.LefschetzNormalization.Geometry.A₄ E R v a ↔
      (Submodule.span ℂ ({GeometricFour.LefschetzNormalization.Geometry.embeddingTensor E a} : Set (GeometricFour.LefschetzNormalization.Geometry.FourTensor E))).map
        (GeometricFour.LefschetzNormalization.Geometry.fourTensorComparison E (fun i => R (v i))
          (CMVariety.Products.CM.Abelian.fourProduct (fun i => (R (v i)).abelianVariety)).variety
          (CMVariety.Products.CM.Abelian.fourProjection _)) ≤
        (CMVariety.Products.CM.Abelian.fourProduct (fun i => (R (v i)).abelianVariety)).variety.complexGeometricAlgebraicClasses 2 := by
  rw [fourTensorLine_image, Submodule.span_singleton_le_iff_mem]
  rfl

/-- Every original normalization clause, with A₄ now the actual geometric
cycle-class image on the specified product and marking. -/
def Normalization (R : GeometricFour.LefschetzNormalization.Geometry.RealizationFamily E) (s : ℕ) (v : LefschetzNormalization.FourTypes E) : Prop :=
  ((¬ ∃ g : LefschetzNormalization.G E, (v 0).val g = true ∧ (v 1).val g = true) ∧
    (∀ τ : LefschetzNormalization.G E, (v 1).val τ = !((v 0).val τ) ∧
      (v 3).val τ = !((v 2).val τ)) ∧ GeometricFour.LefschetzNormalization.Geometry.A₄ E R v (LefschetzNormalization.switchLabels E))
  ∨
  (∃ (g : LefschetzNormalization.G E) (w : LefschetzNormalization.FourTypes E) (d : Fin 4 → LefschetzNormalization.G E → Bool) (reps : Finset (LefschetzNormalization.G E)),
    (∀ i σ, (w i).val σ = (v i).val (σ * g)) ∧
    (∀ i, (w i).val 1 = true) ∧
    (∀ τ : LefschetzNormalization.G E,
      ComplexMultiplication.SignSwitch.CM.signValue ((w 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((w 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((w 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((w 3).val τ)) ∧
    (∀ i, ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i)) (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)) (g⁻¹).toLinearMap) ∧
    (∀ τ : LefschetzNormalization.G E, (g⁻¹).toLinearMap.baseChange ℂ (LefschetzNormalization.embeddingGenerator E τ) =
      LefschetzNormalization.embeddingGenerator E (τ * g)) ∧
    (∀ i τ, d i τ = (w i).val τ⁻¹) ∧
    (∀ i τ, d i (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) = !(d i τ)) ∧
    (1 : LefschetzNormalization.G E) ∈ reps ∧
    (∀ τ : LefschetzNormalization.G E, τ ∈ reps ↔ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps) ∧
    reps.card = s ∧
    (GeometricFour.LefschetzNormalization.Geometry.A₄ E R w (LefschetzNormalization.switchLabels E) ↔ GeometricFour.LefschetzNormalization.Geometry.A₄ E R v (LefschetzNormalization.switchLabels E)) ∧
    ((s = 1 ∧ GeometricFour.LefschetzNormalization.Geometry.A₄ E R v (LefschetzNormalization.switchLabels E)) ∨ 2 ≤ s))

theorem normalization_on_realized_products
    (hDegreeTwo : Conclusions)
    (hExteriorCohomology : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology)
    (hLineBundleCycles : CMReduction.CycleOperations.CM.Construction.LineBundleCyclesInput) (hThomClass : CMReduction.CycleOperations.CM.Construction.ExteriorInput)
    (R : GeometricFour.LefschetzNormalization.Geometry.RealizationFamily E) (s : ℕ)
    (hdegree : Fintype.card (LefschetzNormalization.G E) = 2 * s)
    (v : LefschetzNormalization.FourTypes E)
    (hbalance : ∀ τ : LefschetzNormalization.G E,
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ)) :
    Normalization E R s v := by
  exact LefschetzNormalization.normalization_of_active_embedding E
    scalarTraceInput_proved hDegreeTwo.1 hDegreeTwo.2.1 hDegreeTwo.2.2 s hdegree (GeometricFour.LefschetzNormalization.Geometry.A₂ E R) (GeometricFour.LefschetzNormalization.Geometry.A₄ E R)
    (GeometricFour.LefschetzNormalization.Geometry.A₂_of_balance E R (scalarTraceInput_proved E) hDegreeTwo.2.2)
    (GeometricOperations.LefschetzNormalization.Geometry.A₄_of_pairs E R hLineBundleCycles hThomClass hExteriorCohomology)
    (GeometricFour.LefschetzNormalization.Geometry.A₄_scalar_iff E R)
    (GeometricOperations.LefschetzNormalization.Geometry.A₄_hodge_transfer E R hLineBundleCycles (weightOne_fullness hDegreeTwo.1)) v hbalance

end

end OAI.AlgebraicGeometry.HodgeConjecture.GeometricNormalization.Lefschetz.Geometry
