import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham
import OAI.Analysis.DifferentialForms.Manifold.PullbackLaws

/-! # Manifold De Rham Pullback -/

namespace OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback

noncomputable section

/-!
The cochain and cohomology pullbacks induced by actual smooth manifold maps.
Every degreewise map is the tangent-covector pullback already constructed, and
its compatibility with the exterior derivative is a proved theorem.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

universe u v

variable {E F G : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N P : Type v}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]

/-- Pullback of actual manifold forms assembled into a map of de Rham complexes. -/
def manifoldDeRhamPullback (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ManifoldDeRham.manifoldDeRhamComplex F N ⟶ ManifoldDeRham.manifoldDeRhamComplex E M :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (Algebra.SmoothManifoldForm.pullback f hf))
    (fun n => by
      rw [ManifoldDeRham.manifoldDeRhamComplex_d, ManifoldDeRham.manifoldDeRhamComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro form
      exact Algebra.SmoothManifoldForm.d_pullback f hf form)

@[simp]
theorem manifoldDeRhamPullback_f_apply (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ)
    (form : Algebra.SmoothManifoldForm F N n) :
    (manifoldDeRhamPullback f hf).f n form = Algebra.SmoothManifoldForm.pullback f hf form := rfl

@[simp]
theorem manifoldDeRhamPullback_id :
    manifoldDeRhamPullback (id : M → M) (contMDiff_id (I := 𝓘(ℝ, E))) =
      𝟙 (ManifoldDeRham.manifoldDeRhamComplex E M) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact Algebra.SmoothManifoldForm.pullback_id form

theorem manifoldDeRhamPullback_comp (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (g : N → P)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g) :
    manifoldDeRhamPullback (g ∘ f) (hg.comp hf) =
      manifoldDeRhamPullback g hg ≫ manifoldDeRhamPullback f hf := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact Algebra.SmoothManifoldForm.pullback_comp f hf g hg form

/-- The induced complex-linear map on genuine manifold de Rham cohomology. -/
def manifoldDeRhamCohomologyPullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamCohomology F N n ⟶ ManifoldDeRham.manifoldDeRhamCohomology E M n :=
  HomologicalComplex.homologyMap (manifoldDeRhamPullback f hf) n

@[simp]
theorem manifoldDeRhamCohomologyPullback_id (n : ℕ) :
    manifoldDeRhamCohomologyPullback (id : M → M) (contMDiff_id (I := 𝓘(ℝ, E))) n =
      𝟙 (ManifoldDeRham.manifoldDeRhamCohomology E M n) := by
  change HomologicalComplex.homologyMap
    (manifoldDeRhamPullback (id : M → M) (contMDiff_id (I := 𝓘(ℝ, E)))) n =
      𝟙 ((ManifoldDeRham.manifoldDeRhamComplex E M).homology n)
  rw [manifoldDeRhamPullback_id, HomologicalComplex.homologyMap_id]

theorem manifoldDeRhamCohomologyPullback_comp (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (g : N → P)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g) (n : ℕ) :
    manifoldDeRhamCohomologyPullback (g ∘ f) (hg.comp hf) n =
      manifoldDeRhamCohomologyPullback g hg n ≫ manifoldDeRhamCohomologyPullback f hf n := by
  change HomologicalComplex.homologyMap
      (manifoldDeRhamPullback (g ∘ f) (hg.comp hf)) n =
    HomologicalComplex.homologyMap (manifoldDeRhamPullback g hg) n ≫
      HomologicalComplex.homologyMap (manifoldDeRhamPullback f hf) n
  rw [manifoldDeRhamPullback_comp f hf g hg, HomologicalComplex.homologyMap_comp]

/-- Pullback on categorical cocycles of the genuine manifold complex. -/
def manifoldDeRhamCocyclesPullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamCocycles F N n ⟶ ManifoldDeRham.manifoldDeRhamCocycles E M n :=
  HomologicalComplex.cyclesMap (manifoldDeRhamPullback f hf) n

/-- Taking a closed form's class commutes with the actual pullback. -/
theorem manifoldDeRhamClass_pullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamClass F N n ≫ manifoldDeRhamCohomologyPullback f hf n =
      manifoldDeRhamCocyclesPullback f hf n ≫ ManifoldDeRham.manifoldDeRhamClass E M n :=
  HomologicalComplex.homologyπ_naturality (manifoldDeRhamPullback f hf) n

end

end OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback
