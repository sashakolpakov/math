import OAI.AlgebraicTopology.Cohomology.Singular.SmoothFunctor
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smooth Homotopy -/

namespace OAI.AlgebraicTopology.Cohomology.Singular

noncomputable section

/-!
# Linear contraction of smooth singular simplices

The interval parameter on an n-simplex is the sum of its barycentric coordinates
whose vertices map to 1. It extends to a continuous linear map on the ambient
coordinate space, so a straight-line contraction preserves the required smooth
extension to an open neighborhood of the closed simplex.
-/

open _root_.CategoryTheory Opposite MonoidalCategory
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine interval parameter associated to a map of simplex vertices. -/
def SmoothHomotopy.simplexTimeMap {n : ℕ} (τ : Fin (n + 1) → Fin 2) :
    (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (1 : Fin 2)).comp (Smooth.simplexLinearMap τ)

@[simp]
theorem SmoothHomotopy.simplexTimeMap_apply {n : ℕ} (τ : Fin (n + 1) → Fin 2)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    SmoothHomotopy.simplexTimeMap τ x = (Convexity.StdSimplex.map τ x) 1 :=
  congrArg (fun y : Fin 2 → ℝ => y 1) (Smooth.simplexLinearMap_weights τ x)

theorem SmoothHomotopy.simplexTimeMap_precomp {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1))
    (τ : Fin (n + 1) → Fin 2) (x : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    SmoothHomotopy.simplexTimeMap (τ ∘ θ) x = SmoothHomotopy.simplexTimeMap τ (Convexity.StdSimplex.map θ x) := by
  simp only [SmoothHomotopy.simplexTimeMap_apply, Convexity.StdSimplex.map_comp]

@[simp]
theorem SmoothHomotopy.simplexTimeMap_const_zero {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    SmoothHomotopy.simplexTimeMap (fun _ : Fin (n + 1) => (0 : Fin 2)) x = 0 := by
  rw [SmoothHomotopy.simplexTimeMap_apply, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.weights_map_sum]
  simp

@[simp]
theorem SmoothHomotopy.simplexTimeMap_const_one {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    SmoothHomotopy.simplexTimeMap (fun _ : Fin (n + 1) => (1 : Fin 2)) x = 1 := by
  rw [SmoothHomotopy.simplexTimeMap_apply, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.weights_map_sum]
  simp [Convexity.StdSimplex.total_of_fintype]

/-- The simplex obtained by contracting a simplex linearly toward `c`, with
its interval coordinate prescribed by the vertex map `τ`. -/
def SmoothHomotopy.linearContractionSimplex {n : ℕ} (c : E)
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)) (τ : Fin (n + 1) → Fin 2) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), E) where
  toFun x := (1 - SmoothHomotopy.simplexTimeMap τ x) • σ x + SmoothHomotopy.simplexTimeMap τ x • c
  continuous_toFun := by
    have hc : Continuous (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        (x : Fin (n + 1) → ℝ)) :=
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous
    exact ((continuous_const.sub ((SmoothHomotopy.simplexTimeMap τ).continuous.comp hc)).smul
      σ.continuous).add (((SmoothHomotopy.simplexTimeMap τ).continuous.comp hc).smul continuous_const)

/-- The contraction extends smoothly on the same open neighborhood as `σ`. -/
theorem Smooth.IsSmoothSimplex.linearContraction {n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)} (hσ : Smooth.IsSmoothSimplex σ)
    (c : E) (τ : Fin (n + 1) → Fin 2) :
    Smooth.IsSmoothSimplex (SmoothHomotopy.linearContractionSimplex c σ τ) := by
  rcases hσ with ⟨F, U, hU, hsub, hF, heq⟩
  refine ⟨fun x => (1 - SmoothHomotopy.simplexTimeMap τ x) • F x + SmoothHomotopy.simplexTimeMap τ x • c,
    U, hU, hsub, ?_, ?_⟩
  · exact ((contDiffOn_const.sub (SmoothHomotopy.simplexTimeMap τ).contDiff.contDiffOn).smul hF).add
      ((SmoothHomotopy.simplexTimeMap τ).contDiff.contDiffOn.smul_const c)
  · intro x
    change (1 - SmoothHomotopy.simplexTimeMap τ x) • F x + SmoothHomotopy.simplexTimeMap τ x • c =
      (1 - SmoothHomotopy.simplexTimeMap τ x) • σ x + SmoothHomotopy.simplexTimeMap τ x • c
    rw [heq x]

/-- Simplicial naturality of the explicit contraction formula. -/
theorem SmoothHomotopy.linearContractionSimplex_precomp {m n : ℕ} (c : E)
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E))
    (θ : Fin (m + 1) → Fin (n + 1)) (τ : Fin (n + 1) → Fin 2) :
    SmoothHomotopy.linearContractionSimplex c (σ.comp ⟨Convexity.StdSimplex.map θ, Convexity.StdSimplex.continuous_map ℝ θ⟩)
        (τ ∘ θ) =
      (SmoothHomotopy.linearContractionSimplex c σ τ).comp
        ⟨Convexity.StdSimplex.map θ, Convexity.StdSimplex.continuous_map ℝ θ⟩ := by
  ext x
  change (1 - SmoothHomotopy.simplexTimeMap (τ ∘ θ) x) • σ (Convexity.StdSimplex.map θ x) +
      SmoothHomotopy.simplexTimeMap (τ ∘ θ) x • c =
    (1 - SmoothHomotopy.simplexTimeMap τ (Convexity.StdSimplex.map θ x)) • σ (Convexity.StdSimplex.map θ x) +
      SmoothHomotopy.simplexTimeMap τ (Convexity.StdSimplex.map θ x) • c
  rw [SmoothHomotopy.simplexTimeMap_precomp]

@[simp]
theorem SmoothHomotopy.linearContractionSimplex_zero {n : ℕ} (c : E)
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)) :
    SmoothHomotopy.linearContractionSimplex c σ (fun _ => 0) = σ := by
  ext x
  change (1 - SmoothHomotopy.simplexTimeMap (fun _ => 0) x) • σ x +
    SmoothHomotopy.simplexTimeMap (fun _ => 0) x • c = σ x
  rw [SmoothHomotopy.simplexTimeMap_const_zero]
  simp

@[simp]
theorem SmoothHomotopy.linearContractionSimplex_one {n : ℕ} (c : E)
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)) :
    SmoothHomotopy.linearContractionSimplex c σ (fun _ => 1) = ContinuousMap.const _ c := by
  ext x
  change (1 - SmoothHomotopy.simplexTimeMap (fun _ => 1) x) • σ x +
    SmoothHomotopy.simplexTimeMap (fun _ => 1) x • c = c
  rw [SmoothHomotopy.simplexTimeMap_const_one]
  simp

/-- The linear contraction as an actual morphism from the simplicial cylinder
of smooth singular simplices to smooth singular simplices. -/
def SmoothHomotopy.smoothContractionMap (c : E) :
    (Smooth.smoothSingularSubcomplex E).toSSet ⊗ Δ[1] ⟶
      (Smooth.smoothSingularSubcomplex E).toSSet where
  app n := ↾fun p => ⟨((TopCat.of E).toSSetObjEquiv n).symm
      (SmoothHomotopy.linearContractionSimplex c ((TopCat.of E).toSSetObjEquiv n p.1.val)
        (SSet.stdSimplex.asOrderHom p.2)), by
    change Smooth.IsSmoothSimplex _
    simp only [Equiv.apply_symm_apply]
    exact Smooth.IsSmoothSimplex.linearContraction p.1.property c _⟩
  naturality n m θ := by
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of E).toSSetObjEquiv m).injective
    change SmoothHomotopy.linearContractionSimplex c
        (((TopCat.of E).toSSetObjEquiv n p.1.val).comp
          ⟨Convexity.StdSimplex.map θ.unop, Convexity.StdSimplex.continuous_map ℝ θ.unop⟩)
        ((SSet.stdSimplex.asOrderHom p.2) ∘ θ.unop) =
      (SmoothHomotopy.linearContractionSimplex c ((TopCat.of E).toSSetObjEquiv n p.1.val)
        (SSet.stdSimplex.asOrderHom p.2)).comp
          ⟨Convexity.StdSimplex.map θ.unop, Convexity.StdSimplex.continuous_map ℝ θ.unop⟩
    exact SmoothHomotopy.linearContractionSimplex_precomp c _ _ _

/-- The identity on smooth singular simplices is genuinely simplicially
homotopic to the map induced by the constant smooth map with value `c`. -/
def SmoothHomotopy.smoothLinearContraction (c : E) :
    SSet.Homotopy (𝟙 (Smooth.smoothSingularSubcomplex E).toSSet)
      (SmoothFunctor.smoothSingularMap (fun _ : E => c) contDiff_const) where
  h := SmoothHomotopy.smoothContractionMap c
  h₀ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of E).toSSetObjEquiv n).injective
    change SmoothHomotopy.linearContractionSimplex c ((TopCat.of E).toSSetObjEquiv n p.val)
      (fun _ => 0) = _
    exact SmoothHomotopy.linearContractionSimplex_zero c _
  h₁ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of E).toSSetObjEquiv n).injective
    change SmoothHomotopy.linearContractionSimplex c ((TopCat.of E).toSSetObjEquiv n p.val)
      (fun _ => 1) = _
    exact SmoothHomotopy.linearContractionSimplex_one c _
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular
