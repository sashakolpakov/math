import OAI.AlgebraicGeometry.Comparison.Betti.SingularPresheafPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothNaturality

/-! # Open Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.OpenPullback.Smooth

noncomputable section

/-! Actual smooth pullback on every analytic open set. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : TopCat.{0}} [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : M ⟶ N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

include hf

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem openPreimageMap_smooth (U : Opens N) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (SingularPresheafPullback.openPreimageMap f U) := by
  apply (Topology.Euclidean.OpenCoordinateTransport.Globalization.contMDiff_subtypeVal_comp_iff_order U _).mp
  exact hf.comp (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞))

def analyticOpenPullback (U : Opens N) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex F U ⟶ Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex E ((Opens.map f).obj U) :=
  (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso F U).hom ≫
    Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (SingularPresheafPullback.openPreimageMap f U) (openPreimageMap_smooth f hf U) ≫
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso E ((Opens.map f).obj U)).inv

theorem analyticOpenPullback_intrinsic (U : Opens N) :
    analyticOpenPullback f hf U ≫ (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso E ((Opens.map f).obj U)).hom =
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso F U).hom ≫
        Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (SingularPresheafPullback.openPreimageMap f U) (openPreimageMap_smooth f hf U) := by
  simp only [analyticOpenPullback, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem analyticOpenPullback_restrict {V U : Opens N} (h : V ≤ U) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamRestrict F h ≫ analyticOpenPullback f hf V =
      analyticOpenPullback f hf U ≫
        Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamRestrict E (show (Opens.map f).obj V ≤ (Opens.map f).obj U from fun _ hp => h hp) := by
  let hM : (Opens.map f).obj V ≤ (Opens.map f).obj U := fun _ hp => h hp
  have hc : Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (Opens.inclusion h)
        (contMDiff_inclusion (I := 𝓘(ℝ, F)) (n := ∞) h) ≫
      Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (SingularPresheafPullback.openPreimageMap f V) (openPreimageMap_smooth f hf V) =
    Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (SingularPresheafPullback.openPreimageMap f U) (openPreimageMap_smooth f hf U) ≫
      Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (Opens.inclusion hM)
        (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) hM) := by
    rw [← Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback_comp, ← Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback_comp]
    rfl
  apply (Iso.cancel_iso_hom_right _ _ (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso E ((Opens.map f).obj V))).mp
  rw [Category.assoc, analyticOpenPullback_intrinsic,
    ← Category.assoc, Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso_restrict]
  conv_rhs => rw [Category.assoc, Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso_restrict,
    ← Category.assoc, analyticOpenPullback_intrinsic]
  simpa only [Category.assoc] using congrArg (fun k => (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso F U).hom ≫ k) hc

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.OpenPullback.Smooth
