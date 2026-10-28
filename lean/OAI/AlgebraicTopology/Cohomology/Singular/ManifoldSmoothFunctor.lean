import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth
import OAI.AlgebraicTopology.Cohomology.Singular.Functor
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! # Manifold Smooth Functor -/

namespace OAI.AlgebraicTopology.Cohomology.Singular

noncomputable section

/-!
# Smooth singular functoriality for manifolds

Smooth singular simplices use actual open-neighborhood extensions into a
charted space. A smooth map of charted spaces postcomposes these extensions,
giving genuine simplicial maps and contravariant maps on smooth cochains.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff _root_.Manifold

variable {E F G : Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {M N P : Type}
variable [TopologicalSpace M] [ChartedSpace E M]
variable [TopologicalSpace N] [ChartedSpace F N]
variable [TopologicalSpace P] [ChartedSpace G P]

/-- Smooth postcomposition preserves the actual neighborhood-extension condition. -/
theorem ManifoldSmooth.IsManifoldSmoothSimplex.postcomp {n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)} (hσ : ManifoldSmooth.IsManifoldSmoothSimplex E σ)
    {f : M → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ManifoldSmooth.IsManifoldSmoothSimplex F ((⟨f, hf.continuous⟩ : C(M, N)).comp σ) := by
  rcases hσ with ⟨σ', U, hU, hsub, hσ', heq⟩
  refine ⟨f ∘ σ', U, hU, hsub, hf.comp_contMDiffOn hσ', ?_⟩
  intro x
  exact congrArg f (heq x)

variable (E F) in
/-- The genuine simplicial map on smooth singular simplices induced by a smooth map. -/
def ManifoldSmoothFunctor.manifoldSmoothSingularMap (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet ⟶
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex F N).toSSet where
  app n := ↾fun σ => ⟨(TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val, by
    change ManifoldSmooth.IsManifoldSmoothSimplex F ((TopCat.of N).toSSetObjEquiv n
      ((TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val))
    exact ManifoldSmooth.IsManifoldSmoothSimplex.postcomp σ.property hf⟩
  naturality n m θ := by
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).naturality θ) σ.val

@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothSingularMap_app_val (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : SimplexCategoryᵒᵖ)
    (σ : (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).obj n) :
    ((ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf).app n σ).val =
      (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val := rfl

/-- The image simplex is given by ordinary pointwise postcomposition. -/
@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothSingularMap_apply (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : SimplexCategoryᵒᵖ)
    (σ : (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).obj n)
    (x : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (TopCat.of N).toSSetObjEquiv n ((ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf).app n σ).val x =
      f ((TopCat.of M).toSSetObjEquiv n σ.val x) := rfl

/-- Inclusion into continuous singular simplices is natural for smooth maps. -/
@[reassoc]
theorem ManifoldSmoothFunctor.manifoldSmoothSingularMap_inclusion (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf ≫ ManifoldSmooth.manifoldSmoothInclusion F N =
      ManifoldSmooth.manifoldSmoothInclusion E M ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩) := rfl

@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothSingularMap_id :
    ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (id : M → M) contMDiff_id =
      𝟙 (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet := by
  ext n σ
  apply Subtype.ext
  rfl

@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothSingularMap_comp (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (g : N → P)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g) :
    ManifoldSmoothFunctor.manifoldSmoothSingularMap E G (g ∘ f) (hg.comp hf) =
      ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf ≫ ManifoldSmoothFunctor.manifoldSmoothSingularMap F G g hg := by
  ext n σ
  apply Subtype.ext
  rfl

variable {R : Type} [Ring R]

variable (E F) in
/-- Pullback of genuine smooth singular cochains along a smooth map of manifolds. -/
def ManifoldSmoothFunctor.manifoldSmoothPullback (A : ModuleCat.{0} R) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ManifoldSmooth.manifoldSmoothCochains F A N ⟶ ManifoldSmooth.manifoldSmoothCochains E A M :=
  Functor.simplicialPullback A (ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf)

@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothPullback_id (A : ModuleCat.{0} R) :
    ManifoldSmoothFunctor.manifoldSmoothPullback E E A (id : M → M) contMDiff_id =
      𝟙 (ManifoldSmooth.manifoldSmoothCochains E A M) := by
  simp [ManifoldSmoothFunctor.manifoldSmoothPullback]

@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothPullback_comp (A : ModuleCat.{0} R) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (g : N → P)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g) :
    ManifoldSmoothFunctor.manifoldSmoothPullback E G A (g ∘ f) (hg.comp hf) =
      ManifoldSmoothFunctor.manifoldSmoothPullback F G A g hg ≫ ManifoldSmoothFunctor.manifoldSmoothPullback E F A f hf := by
  exact (congrArg (fun k => Functor.simplicialPullback A k)
    (ManifoldSmoothFunctor.manifoldSmoothSingularMap_comp f hf g hg)).trans (Functor.simplicialPullback_comp A _ _)

/-- Ordinary-to-smooth cochain restriction commutes with smooth pullback. -/
@[reassoc]
theorem ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality (A : ModuleCat.{0} R)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    Functor.singularPullback A (TopCat.ofHom ⟨f, hf.continuous⟩) ≫
        ManifoldSmooth.manifoldSmoothCochainRestriction E A M =
      ManifoldSmooth.manifoldSmoothCochainRestriction F A N ≫ ManifoldSmoothFunctor.manifoldSmoothPullback E F A f hf := by
  change Functor.simplicialPullback A (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) ≫
      Functor.simplicialPullback A (ManifoldSmooth.manifoldSmoothInclusion E M) =
    Functor.simplicialPullback A (ManifoldSmooth.manifoldSmoothInclusion F N) ≫
      Functor.simplicialPullback A (ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf)
  rw [← Functor.simplicialPullback_comp, ← Functor.simplicialPullback_comp,
    ManifoldSmoothFunctor.manifoldSmoothSingularMap_inclusion]

end

end OAI.AlgebraicTopology.Cohomology.Singular
