import OAI.AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison
import OAI.AlgebraicTopology.Cohomology.Singular.Homotopy
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! # Translation Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianVariety.TranslationCohomology.Constructions.Exterior

noncomputable section

/-!
# Translation invariance on cohomology for ExteriorCohomology

A path from the identity to a group element gives a genuine homotopy of
translations. The established smooth-singular restriction comparison transfers
this homotopy invariance to actual integration cocycles.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]

def leftTranslationTop (g : G) : TopCat.of G ⟶ TopCat.of G :=
  TopCat.ofHom ⟨(fun h : G => g * h),
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)).continuous⟩

def leftTranslationHomotopy [ConnectedSpace G] (g : G) :
    TopCat.Homotopy (𝟙 (TopCat.of G)) (leftTranslationTop (E := E) g) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ, E)) (n := ∞)
  let : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace E G
  let : PathConnectedSpace G := PathConnectedSpace.of_locallyPathConnectedSpace
  let γ : Path (1 : G) g := (PathConnectedSpace.joined 1 g).somePath
  exact
    { toFun := fun p => γ p.1 * p.2
      continuous_toFun := (γ.continuous.comp continuous_fst).mul continuous_snd
      map_zero_left := fun h => by simp
      map_one_left := fun h => by simp [leftTranslationTop] }

theorem leftTranslation_singularCohomology [ConnectedSpace G] (g : G) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) (leftTranslationTop (E := E) g) n =
      𝟙 _ := by
  have h := AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyPullback_eq (ModuleCat.of ℂ ℂ) (leftTranslationHomotopy (E := E) g) n
  rw [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id] at h
  exact h.symm

theorem leftTranslation_smoothCohomology [ConnectedSpace G] (g : G) (n : ℕ) :
    HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E E (ModuleCat.of ℂ ℂ) (fun h : G => g * h)
        (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞))) n = 𝟙 _ := by
  let e := AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso E G n
  apply (cancel_epi e.hom).mp
  rw [Category.comp_id]
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality (ModuleCat.of ℂ ℂ)
      (fun h : G => g * h) (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)))
  simp only [HomologicalComplex.homologyMap_comp] at h
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) (leftTranslationTop (E := E) g) n ≫
    e.hom = e.hom ≫ _ at h
  rw [leftTranslation_singularCohomology, Category.id_comp] at h
  exact h.symm

theorem leftTranslation_integrationClass [ConnectedSpace G] (g : G) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) G) n
      (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E G n
        (Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (fun h : G => g * h)
          (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) n form)) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) G) n
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E G n form) := by
  let f := AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E E (ModuleCat.of ℂ ℂ) (fun h : G => g * h)
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞))
  have hc : AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E G n
      (Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (fun h : G => g * h)
        (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) n form) =
      AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap f n (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E G n form) := by
    apply Subtype.ext
    have hn := AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_naturality (E := E) (F := E) (M := G) (N := G)
      (fun h : G => g * h) (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) n
    exact congrArg (fun q : ModuleCat.of ℂ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) ⟶
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) G).X n => q.hom form.val) hn
  rw [hc, ← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  exact ConcreteCategory.congr_hom (leftTranslation_smoothCohomology (E := E) g n) _

end

end OAI.AlgebraicGeometry.AbelianVariety.TranslationCohomology.Constructions.Exterior
