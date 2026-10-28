import OAI.AlgebraicGeometry.Comparison.Betti.Open.EvaluationNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothForms
import OAI.Topology.Euclidean.OpenCoordinateTransport

/-! # Smooth Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothNaturality

noncomputable section

/-!
# Naturality of the actual smooth realization on inverse-image opens

The pullback below is the tangent-covector pullback of the original map on
complex points, transported between ambient and intrinsic open forms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

theorem analyticOpenMap_smooth (U : Y.left.Opens) (W : X.left.Opens)
    (hWU : W ≤ f.left ⁻¹ᵁ U) :
    ContMDiff 𝓘(ℝ, RegularSmoothness.NativeModel X) 𝓘(ℝ, RegularSmoothness.NativeModel Y) ∞ (EvaluationNaturality.analyticOpenMap f U W hWU) := by
  apply (Topology.Euclidean.OpenCoordinateTransport.Globalization.contMDiff_subtypeVal_comp_iff_order (AffineIsoEvaluation.analyticOpen Y U) _).mp
  exact (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞).comp
    (contMDiff_subtype_val (I := 𝓘(ℝ, RegularSmoothness.NativeModel X)) (n := ∞))

/-- Pullback of actual smooth forms on analytic inverse-image opens. -/
def openSmoothPullback (U : Y.left.Opens) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex (RegularSmoothness.NativeModel Y) (AffineIsoEvaluation.analyticOpen Y U) ⟶
      Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) :=
  (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso (RegularSmoothness.NativeModel Y) (AffineIsoEvaluation.analyticOpen Y U)).hom ≫
    Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (EvaluationNaturality.analyticOpenMap f U (f.left ⁻¹ᵁ U) le_rfl)
      (analyticOpenMap_smooth f U (f.left ⁻¹ᵁ U) le_rfl) ≫
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U))).inv

theorem openSmoothPullback_intrinsic (U : Y.left.Opens) :
    openSmoothPullback f U ≫
        (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U))).hom =
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso (RegularSmoothness.NativeModel Y) (AffineIsoEvaluation.analyticOpen Y U)).hom ≫
        Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (EvaluationNaturality.analyticOpenMap f U (f.left ⁻¹ᵁ U) le_rfl)
          (analyticOpenMap_smooth f U (f.left ⁻¹ᵁ U) le_rfl) := by
  simp only [openSmoothPullback, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Realization commutes with pullback on every open and in every degree. -/
theorem openSmoothFormMap_naturality (U : Y.left.Opens) (n : ℕ)
    (a : Algebraic.Forms.Form Γ(Y.left, U) n) :
    SmoothForms.openSmoothFormMap X (f.left ⁻¹ᵁ U) n (Algebraic.Forms.pullback (Algebraic.Sheaves.sectionPullback f U) n a) =
      (openSmoothPullback f U).f n (SmoothForms.openSmoothFormMap Y U n a) := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) n).injective
  change (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) n)
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) n).symm
        (Betti.Smooth.CochainMap.smoothFormMap (AffineIsoEvaluation.sectionEvaluationOn X (f.left ⁻¹ᵁ U))
          (SmoothEvaluation.sectionEvaluationOn_smooth X (f.left ⁻¹ᵁ U)) n
          (Algebraic.Forms.pullback (Algebraic.Sheaves.sectionPullback f U) n a))) =
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) n)
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) n).symm
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (EvaluationNaturality.analyticOpenMap f U (f.left ⁻¹ᵁ U) le_rfl)
          (analyticOpenMap_smooth f U (f.left ⁻¹ᵁ U) le_rfl)
          ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel Y) (AffineIsoEvaluation.analyticOpen Y U) n)
            ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel Y) (AffineIsoEvaluation.analyticOpen Y U) n).symm
              (Betti.Smooth.CochainMap.smoothFormMap (AffineIsoEvaluation.sectionEvaluationOn Y U)
                (SmoothEvaluation.sectionEvaluationOn_smooth Y U) n a)))))
  simp only [LinearEquiv.apply_symm_apply]
  exact Betti.Smooth.CochainNaturality.smoothFormMap_naturality
    (AffineIsoEvaluation.sectionEvaluationOn X (f.left ⁻¹ᵁ U)) (SmoothEvaluation.sectionEvaluationOn_smooth X (f.left ⁻¹ᵁ U))
    (AffineIsoEvaluation.sectionEvaluationOn Y U) (SmoothEvaluation.sectionEvaluationOn_smooth Y U)
    (Algebraic.Sheaves.sectionPullback f U) (EvaluationNaturality.analyticOpenMap f U (f.left ⁻¹ᵁ U) le_rfl)
    (analyticOpenMap_smooth f U (f.left ⁻¹ᵁ U) le_rfl)
    (EvaluationNaturality.sectionEvaluationOn_pullback f U) n a

theorem openSmoothCochainMap_naturality (U : Y.left.Opens) :
    Algebraic.Forms.complexPullback (Algebraic.Sheaves.sectionPullback f U) ≫
        SmoothForms.openSmoothCochainMap X (f.left ⁻¹ᵁ U) =
      SmoothForms.openSmoothCochainMap Y U ≫ openSmoothPullback f U := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact openSmoothFormMap_naturality f U n

/-- The genuine smooth pullbacks form a morphism of presheaves of complexes. -/
theorem openSmoothPullback_restrict {V U : Y.left.Opens} (h : V ≤ U) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamRestrict (RegularSmoothness.NativeModel Y) (SmoothForms.analyticOpen_mono Y h) ≫
        openSmoothPullback f V =
      openSmoothPullback f U ≫
        Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamRestrict (RegularSmoothness.NativeModel X)
          (SmoothForms.analyticOpen_mono X (show f.left ⁻¹ᵁ V ≤ f.left ⁻¹ᵁ U from fun _ hp => h hp)) := by
  let hX : f.left ⁻¹ᵁ V ≤ f.left ⁻¹ᵁ U := fun _ hp => h hp
  have hcomp :
      Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (Opens.inclusion (SmoothForms.analyticOpen_mono Y h))
          (contMDiff_inclusion (I := 𝓘(ℝ, RegularSmoothness.NativeModel Y)) (n := ∞) _) ≫
        Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (EvaluationNaturality.analyticOpenMap f V (f.left ⁻¹ᵁ V) le_rfl)
          (analyticOpenMap_smooth f V (f.left ⁻¹ᵁ V) le_rfl) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (EvaluationNaturality.analyticOpenMap f U (f.left ⁻¹ᵁ U) le_rfl)
          (analyticOpenMap_smooth f U (f.left ⁻¹ᵁ U) le_rfl) ≫
        Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (Opens.inclusion (SmoothForms.analyticOpen_mono X hX))
          (contMDiff_inclusion (I := 𝓘(ℝ, RegularSmoothness.NativeModel X)) (n := ∞) _) := by
    rw [← Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback_comp, ← Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback_comp]
    rfl
  apply (cancel_mono
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ V))).hom).mp
  rw [Category.assoc, openSmoothPullback_intrinsic,
    ← Category.assoc, Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso_restrict]
  conv_rhs => rw [Category.assoc, Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso_restrict,
    ← Category.assoc, openSmoothPullback_intrinsic]
  simpa only [Category.assoc] using congrArg
    (fun k => (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso (RegularSmoothness.NativeModel Y) (AffineIsoEvaluation.analyticOpen Y U)).hom ≫ k) hcomp

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothNaturality
