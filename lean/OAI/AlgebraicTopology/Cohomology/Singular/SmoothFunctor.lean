import OAI.AlgebraicTopology.Cohomology.Singular.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Smooth Functor -/

namespace OAI.AlgebraicTopology.Cohomology.Singular

noncomputable section

/-!
# Functoriality of smooth singular simplices

A globally smooth map between real normed spaces postcomposes every smooth
singular simplex. The resulting simplicial map commutes with the actual
inclusion into the ordinary continuous singular simplicial set.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff

variable {E F G : Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Postcomposition by a globally smooth map preserves smooth simplex extensions. -/
theorem Smooth.IsSmoothSimplex.postcomp {n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)} (hσ : Smooth.IsSmoothSimplex σ)
    {f : E → F} (hf : ContDiff ℝ ∞ f) :
    Smooth.IsSmoothSimplex ((⟨f, hf.continuous⟩ : C(E, F)).comp σ) := by
  rcases hσ with ⟨σ', U, hU, hsub, hσ', heq⟩
  refine ⟨f ∘ σ', U, hU, hsub, hf.comp_contDiffOn hσ', ?_⟩
  intro x
  exact congrArg f (heq x)

/-- The simplicial map on smooth singular simplices induced by a smooth map. -/
def SmoothFunctor.smoothSingularMap (f : E → F) (hf : ContDiff ℝ ∞ f) :
    (Smooth.smoothSingularSubcomplex E).toSSet ⟶ (Smooth.smoothSingularSubcomplex F).toSSet where
  app n := ↾fun σ => ⟨(TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val, by
    change Smooth.IsSmoothSimplex ((TopCat.of F).toSSetObjEquiv n
      ((TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val))
    exact Smooth.IsSmoothSimplex.postcomp σ.property hf⟩
  naturality n m θ := by
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).naturality θ) σ.val

/-- The smooth simplicial map is ordinary postcomposition on underlying simplices. -/
@[simp]
theorem SmoothFunctor.smoothSingularMap_app_val (f : E → F) (hf : ContDiff ℝ ∞ f)
    (n : SimplexCategoryᵒᵖ) (σ : (Smooth.smoothSingularSubcomplex E).obj n) :
    ((SmoothFunctor.smoothSingularMap f hf).app n σ).val =
      (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val := rfl

/-- Evaluating the image simplex is pointwise postcomposition by the smooth map. -/
@[simp]
theorem SmoothFunctor.smoothSingularMap_apply (f : E → F) (hf : ContDiff ℝ ∞ f)
    (n : SimplexCategoryᵒᵖ) (σ : (Smooth.smoothSingularSubcomplex E).obj n)
    (x : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (TopCat.of F).toSSetObjEquiv n ((SmoothFunctor.smoothSingularMap f hf).app n σ).val x =
      f ((TopCat.of E).toSSetObjEquiv n σ.val x) := rfl

/-- Inclusion of smooth simplices is natural with respect to smooth maps. -/
@[reassoc]
theorem SmoothFunctor.smoothSingularMap_inclusion (f : E → F) (hf : ContDiff ℝ ∞ f) :
    SmoothFunctor.smoothSingularMap f hf ≫ Smooth.smoothSingularInclusion F =
      Smooth.smoothSingularInclusion E ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩) := rfl

@[simp]
theorem SmoothFunctor.smoothSingularMap_id :
    SmoothFunctor.smoothSingularMap (id : E → E) contDiff_id =
      𝟙 (Smooth.smoothSingularSubcomplex E).toSSet := by
  ext n σ
  apply Subtype.ext
  rfl

@[simp]
theorem SmoothFunctor.smoothSingularMap_comp (f : E → F) (hf : ContDiff ℝ ∞ f)
    (g : F → G) (hg : ContDiff ℝ ∞ g) :
    SmoothFunctor.smoothSingularMap (g ∘ f) (hg.comp hf) =
      SmoothFunctor.smoothSingularMap f hf ≫ SmoothFunctor.smoothSingularMap g hg := by
  ext n σ
  apply Subtype.ext
  rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular
