import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration
import OAI.Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph
import OAI.AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison

/-! # Smooth Simplex Diffeomorph -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexDiffeomorph

noncomputable section

/-!
# Diffeomorphism invariance of actual smooth-simplex integration

The genuine Duffy integration cochain map is natural for smooth maps.
Combining that proved naturality with the actual pullback isomorphisms
gives an isomorphism of arrows for every smooth diffeomorphism. The same
construction applies to ambient-local forms through the checked intrinsic
open-manifold de Rham isomorphism.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison
open scoped _root_.Manifold ContDiff

variable {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

set_option backward.isDefEq.respectTransparency false in
/-- Diffeomorphism pullback identifies the actual integration arrows,
including their concrete form and smooth-singular-cochain maps. -/
def smoothSimplexIntegrationDiffeomorphArrowIso
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) :
    Arrow.mk (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap F N) ≅
      Arrow.mk (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) :=
  Arrow.isoMk (Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph.manifoldDeRhamDiffeomorph e)
    (Cohomology.Singular.ChartSmoothComparison.manifoldSmoothCochainsDiffeomorphIso (ModuleCat.of ℂ ℂ) e)
    (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap_naturality e e.contMDiff)

/-- The source part of the arrow isomorphism is actual form pullback. -/
@[simp]
theorem smoothSimplexIntegrationDiffeomorphArrowIso_hom_left
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) :
    (smoothSimplexIntegrationDiffeomorphArrowIso e).hom.left =
      Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback e e.contMDiff := rfl

/-- The target part is pullback on the actual smooth singular cochains. -/
@[simp]
theorem smoothSimplexIntegrationDiffeomorphArrowIso_hom_right
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) :
    (smoothSimplexIntegrationDiffeomorphArrowIso e).hom.right =
      Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E F (ModuleCat.of ℂ ℂ) e e.contMDiff := rfl

/-- The genuine smooth-simplex integration map is a quasi-isomorphism
on one side of a smooth diffeomorphism exactly when it is on the other. -/
theorem quasiIso_smoothSimplexIntegration_diffeomorph_iff
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) :
    QuasiIso (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap F N) ↔
      QuasiIso (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) :=
  quasiIso_iff_of_arrow_mk_iso _ _ (smoothSimplexIntegrationDiffeomorphArrowIso e)

variable (E) in
/-- Ambient-local and intrinsic open-manifold integration are the same
arrow after the proven de Rham source identification. -/
def manifoldOpenIntegrationIntrinsicArrowIso (U : Opens M) :
    Arrow.mk (ManifoldOpenIntegration.manifoldOpenIntegration E U) ≅
      Arrow.mk (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E U) :=
  Arrow.isoMk (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso E U)
    (Iso.refl (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) U)) (by
      change (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso E U).hom ≫ SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E U =
        ManifoldOpenIntegration.manifoldOpenIntegration E U ≫ 𝟙 _
      rw [Category.comp_id]
      rfl)

variable (E) in
/-- The actual ambient-local integration map has the quasi-isomorphism
property exactly when its intrinsic open-manifold presentation does. -/
theorem quasiIso_manifoldOpenIntegration_iff (U : Opens M) :
    QuasiIso (ManifoldOpenIntegration.manifoldOpenIntegration E U) ↔
      QuasiIso (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E U) :=
  quasiIso_iff_of_arrow_mk_iso _ _ (manifoldOpenIntegrationIntrinsicArrowIso E U)

/-- Any actual diffeomorphism between open submanifolds identifies their
ambient-local integration arrows. The sources use the genuine intrinsic-open
form equivalences and the target maps are smooth-singular pullbacks. -/
def manifoldOpenIntegrationDiffeomorphArrowIso (U : Opens M) (V : Opens N)
    (e : U ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ V) :
    Arrow.mk (ManifoldOpenIntegration.manifoldOpenIntegration F V) ≅
      Arrow.mk (ManifoldOpenIntegration.manifoldOpenIntegration E U) :=
  manifoldOpenIntegrationIntrinsicArrowIso F V ≪≫
    smoothSimplexIntegrationDiffeomorphArrowIso e ≪≫
      (manifoldOpenIntegrationIntrinsicArrowIso E U).symm

/-- Transfer of the genuine open-domain integration comparison across
an arbitrary smooth diffeomorphism, in particular an actual chart map. -/
theorem quasiIso_manifoldOpenIntegration_diffeomorph_iff (U : Opens M) (V : Opens N)
    (e : U ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ V) :
    QuasiIso (ManifoldOpenIntegration.manifoldOpenIntegration F V) ↔ QuasiIso (ManifoldOpenIntegration.manifoldOpenIntegration E U) :=
  quasiIso_iff_of_arrow_mk_iso _ _ (manifoldOpenIntegrationDiffeomorphArrowIso U V e)

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexDiffeomorph
