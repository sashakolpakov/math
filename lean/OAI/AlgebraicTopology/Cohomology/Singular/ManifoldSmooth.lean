import OAI.AlgebraicTopology.Cohomology.Singular.Smooth
import OAI.AlgebraicTopology.Cohomology.Singular.Functor
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Manifold Smooth -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth

noncomputable section

/-!
# Genuine smooth singular simplices in charted manifolds

The target now has its actual manifold smooth structure. A simplex is smooth
when it extends to an open neighborhood of the closed standard simplex as a
`ContMDiffOn` map. This uses the usual model without boundary and does not put a
spurious linear structure on the manifold. The construction is meaningful for
a charted space, and has its usual interpretation for a smooth atlas.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff _root_.Manifold

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- A manifold-valued simplex with an actual smooth neighborhood extension. -/
def IsManifoldSmoothSimplex {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)) : Prop :=
  ∃ (F : (Fin (n + 1) → ℝ) → M) (U : Set (Fin (n + 1) → ℝ)),
    IsOpen U ∧ Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      (x : Fin (n + 1) → ℝ)) ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, E) ∞ F U ∧
        ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)), F x = σ x

theorem IsManifoldSmoothSimplex.precomp {m n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)}
    (hσ : IsManifoldSmoothSimplex E σ) (f : Fin (m + 1) → Fin (n + 1)) :
    IsManifoldSmoothSimplex E
      (σ.comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩) := by
  rcases hσ with ⟨F, U, hU, hsub, hF, heq⟩
  refine ⟨F ∘ Smooth.simplexLinearMap f, (Smooth.simplexLinearMap f) ⁻¹' U,
    hU.preimage (Smooth.simplexLinearMap f).continuous, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hsub ⟨Convexity.StdSimplex.map f x, (Smooth.simplexLinearMap_weights f x).symm⟩
  · exact hF.comp (Smooth.simplexLinearMap f).contDiff.contMDiff.contMDiffOn
      (Set.mapsTo_preimage _ _)
  · intro x
    change F (Smooth.simplexLinearMap f x) = σ (Convexity.StdSimplex.map f x)
    rw [Smooth.simplexLinearMap_weights]
    exact heq (Convexity.StdSimplex.map f x)

/-- Constant simplices have constant smooth manifold-valued extensions. -/
theorem isManifoldSmoothSimplex_const (n : ℕ) (x : M) :
    IsManifoldSmoothSimplex E (ContinuousMap.const (Convexity.StdSimplex ℝ (Fin (n + 1))) x) := by
  exact ⟨fun _ => x, Set.univ, isOpen_univ, Set.subset_univ _,
    contMDiffOn_const, fun _ => rfl⟩

/-- The genuine simplicial subcomplex of manifold-smooth singular simplices. -/
def manifoldSmoothSingularSubcomplex (M : Type) [TopologicalSpace M] [ChartedSpace E M] :
    (TopCat.toSSet.obj (TopCat.of M)).Subcomplex where
  obj n := {σ | IsManifoldSmoothSimplex E ((TopCat.of M).toSSetObjEquiv n σ)}
  map {m n} f σ hσ := by
    change IsManifoldSmoothSimplex E ((TopCat.of M).toSSetObjEquiv n
      ((TopCat.toSSet.obj (TopCat.of M)).map f σ))
    have h := IsManifoldSmoothSimplex.precomp E
      (σ := (TopCat.of M).toSSetObjEquiv m σ) hσ f.unop
    convert h using 1
    ext x
    rfl

/-- The actual inclusion forgetting only the smoothness property. -/
abbrev manifoldSmoothInclusion (M : Type) [TopologicalSpace M] [ChartedSpace E M] :
    (manifoldSmoothSingularSubcomplex E M).toSSet ⟶ TopCat.toSSet.obj (TopCat.of M) :=
  (manifoldSmoothSingularSubcomplex E M).ι

variable {R : Type} [Ring R]

/-- Smooth singular cochains of the genuine smooth simplicial set. -/
abbrev manifoldSmoothCochains (A : ModuleCat.{0} R)
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  Basic.simplicialCochains (manifoldSmoothSingularSubcomplex E M).toSSet A

/-- Restrict a continuous singular cochain to manifold-smooth simplices. -/
def manifoldSmoothCochainRestriction (A : ModuleCat.{0} R)
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] :
    Basic.singularCochains A (TopCat.of M) ⟶ manifoldSmoothCochains E A M :=
  Functor.simplicialPullback A (manifoldSmoothInclusion E M)

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth
