import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import Mathlib.Topology.Algebra.Monoid.FunOnFinite
import OAI.AlgebraicTopology.Cohomology.Singular.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Smooth -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Smooth

noncomputable section

/-!
# Smooth singular simplices in a real normed space

A smooth simplex is a continuous simplex that extends smoothly to an open
neighborhood of the standard simplex in its ambient coordinate space. This is
the usual extendibility condition at the boundary; no differentiability of a
function on a bare subtype is substituted for it.

The extension condition is preserved by every simplicial operator, since the
standard simplex maps extend to continuous linear maps of coordinate spaces.
Consequently these simplices form an actual subcomplex of the continuous
singular simplicial set. No quasi-isomorphism assertion is made here.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial ContDiff OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth extension to an open neighborhood of the closed standard simplex. -/
def IsSmoothSimplex {n : ℕ} (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)) : Prop :=
  ∃ (F : (Fin (n + 1) → ℝ) → E) (U : Set (Fin (n + 1) → ℝ)),
    IsOpen U ∧ Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) => (x : Fin (n + 1) → ℝ)) ⊆ U ∧
      ContDiffOn ℝ ∞ F U ∧ ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)), F x = σ x

/-- The ambient continuous linear extension of a simplex operator. -/
def simplexLinearMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    (Fin (m + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) where
  toLinearMap := FunOnFinite.linearMap ℝ ℝ f
  cont := FunOnFinite.continuous_linearMap ℝ ℝ f

theorem simplexLinearMap_weights {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1)) (x : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    simplexLinearMap f x = (Convexity.StdSimplex.map f x : Fin (n + 1) → ℝ) := by
  simp [simplexLinearMap, FunOnFinite.linearMap, Convexity.StdSimplex.map]
  rfl

theorem IsSmoothSimplex.precomp {m n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)} (hσ : IsSmoothSimplex σ)
    (f : Fin (m + 1) → Fin (n + 1)) :
    IsSmoothSimplex (σ.comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩) := by
  rcases hσ with ⟨F, U, hU, hsub, hF, heq⟩
  refine ⟨F ∘ simplexLinearMap f, (simplexLinearMap f) ⁻¹' U,
    hU.preimage (simplexLinearMap f).continuous, ?_,
    hF.comp_continuousLinearMap (simplexLinearMap f), ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hsub ⟨Convexity.StdSimplex.map f x, (simplexLinearMap_weights f x).symm⟩
  · intro x
    change F (simplexLinearMap f x) = σ (Convexity.StdSimplex.map f x)
    rw [simplexLinearMap_weights]
    exact heq (Convexity.StdSimplex.map f x)

/-- Constant simplices have globally smooth extensions. -/
theorem isSmoothSimplex_const (n : ℕ) (x : E) :
    IsSmoothSimplex (ContinuousMap.const (Convexity.StdSimplex ℝ (Fin (n + 1))) x) := by
  exact ⟨fun _ => x, Set.univ, isOpen_univ, Set.subset_univ _,
    contDiffOn_const, fun _ => rfl⟩

/-- Smooth simplices form a simplicial subcomplex of genuine singular simplices. -/
def smoothSingularSubcomplex (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (TopCat.toSSet.obj (TopCat.of E)).Subcomplex where
  obj n := {σ | IsSmoothSimplex ((TopCat.of E).toSSetObjEquiv n σ)}
  map {m n} f σ hσ := by
    change IsSmoothSimplex ((TopCat.of E).toSSetObjEquiv n
      ((TopCat.toSSet.obj (TopCat.of E)).map f σ))
    have h := IsSmoothSimplex.precomp
      (σ := (TopCat.of E).toSSetObjEquiv m σ) hσ f.unop
    convert h using 1
    ext x
    rfl

/-- The actual simplicial inclusion of smooth into continuous singular simplices. -/
abbrev smoothSingularInclusion (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (smoothSingularSubcomplex E).toSSet ⟶ TopCat.toSSet.obj (TopCat.of E) :=
  (smoothSingularSubcomplex E).ι

variable {R : Type} [Ring R]

/-- Smooth singular chains with coefficients in a module. -/
abbrev smoothSingularChains (M : ModuleCat.{0} R)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  (smoothSingularSubcomplex E).toSSet.chainComplex M

/-- The genuine comparison map on chains induced by inclusion of smooth simplices. -/
def smoothSingularChainInclusion (M : ModuleCat.{0} R)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    smoothSingularChains M E ⟶ (TopCat.toSSet.obj (TopCat.of E)).chainComplex M :=
  SSet.chainComplexMap (smoothSingularInclusion E) M

/-- Smooth singular cochains, using products over the actual smooth simplices. -/
abbrev smoothSingularCochains (M : ModuleCat.{0} R)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  Singular.Basic.simplicialCochains (smoothSingularSubcomplex E).toSSet M

/-- Restrict an ordinary singular cochain to its smooth simplices. -/
def smoothSingularCochainRestriction (M : ModuleCat.{0} R)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Singular.Basic.singularCochains M (TopCat.of E) ⟶ smoothSingularCochains M E :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    (SSet.chainComplexMap (smoothSingularInclusion E) (op M)).op

end

end OAI.AlgebraicTopology.Cohomology.Singular.Smooth
