import OAI.AlgebraicGeometry.Albanese.Construction.InvariantOneForms
import OAI.AlgebraicGeometry.AbelianVariety.AnalyticGroup
import OAI.AlgebraicGeometry.Albanese.Construction.Smooth

/-! # Analytic Pullback -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.AnalyticPullback

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianVariety.AnalyticGroup.Constructions.ExteriorCohomology

/-- The model of the native complex-point manifold of an integral smooth scheme. -/
abbrev nativeModel (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] :=
  Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

variable {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral Z.left] [Smooth Z.hom]

/-- Pullback along the actual analytic map induced by a scheme morphism. -/
def nativePullback (f : X ⟶ Y) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (nativeModel Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (nativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) n :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞)

theorem nativePullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (nativeModel Z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z) n) :
    nativePullback (f ≫ g) n form = nativePullback f n (nativePullback g n form) := by
  have hmap : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (f ≫ g) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f := by
    funext p
    exact (Category.assoc p f g).symm
  unfold nativePullback
  rw! [hmap]
  exact Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp _ _ _ _ form

theorem nativePullback_comp_zero (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (nativeModel Z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z) n)
    (hg : nativePullback g n form = 0) : nativePullback (f ≫ g) n form = 0 := by
  rw [nativePullback_comp, hg, map_zero]

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

instance abelianOver_integral : IsIntegral A.toOver.left := A.variety.property
instance abelianOver_smooth : Smooth A.toOver.hom := A.variety.presentation.smooth

/-- A constant identity-valued scheme map pulls every one-form back to zero. -/
theorem nativePullback_one
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm A.variety.analyticModel A.variety.analyticSpace 1) :
    nativePullback (1 : X ⟶ A.toOver) 1 form = 0 := by
  have hmap : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (1 : X ⟶ A.toOver) = fun _ => 1 := by
    funext p
    exact MonObj.comp_one p
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  change form ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (1 : X ⟶ A.toOver)) x)
    (fun i => mfderiv 𝓘(ℝ, nativeModel X) 𝓘(ℝ, A.variety.analyticModel)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (1 : X ⟶ A.toOver)) x (v i)) = 0
  rw [hmap, mfderiv_const]
  exact (form 1).map_zero

/-- Vanishing of an invariant one-form's pullback is preserved by pointwise
multiplication of actual algebraic maps. -/
theorem nativePullback_mul_zero
    (form : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1)
    (f g : X ⟶ A.toOver) (hf : nativePullback f 1 form.val = 0)
    (hg : nativePullback g 1 form.val = 0) : nativePullback (f * g) 1 form.val = 0 := by
  have hmap : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (f * g) =
      fun p => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p * ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g p := by
    funext p
    exact MonObj.comp_mul p f g
  unfold nativePullback
  rw! [hmap]
  exact InvariantOneForms.invariantOneForm_pullback_mul_zero form _ _
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map g ∞) hf hg

theorem nativePullback_inv_zero
    (form : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1)
    (f : X ⟶ A.toOver) (hf : nativePullback f 1 form.val = 0) :
    nativePullback f⁻¹ 1 form.val = 0 := by
  have hmap : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f⁻¹ = fun p => (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)⁻¹ := by
    funext p
    exact GrpObj.comp_inv p f
  unfold nativePullback
  rw! [hmap]
  exact InvariantOneForms.invariantOneForm_pullback_inv_zero form _ (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞) hf

theorem nativePullback_div_zero
    (form : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1)
    (f g : X ⟶ A.toOver) (hf : nativePullback f 1 form.val = 0)
    (hg : nativePullback g 1 form.val = 0) : nativePullback (f / g) 1 form.val = 0 := by
  rw [div_eq_mul_inv]
  exact nativePullback_mul_zero A form f g⁻¹ hf (nativePullback_inv_zero A form g hg)

end

end OAI.AlgebraicGeometry.Albanese.Construction.AnalyticPullback
